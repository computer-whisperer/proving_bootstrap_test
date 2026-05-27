//! M4 — a minimal *structured* wasm VM, in the object language, and the in-place
//! reverse expressed as wasm. The VM runs (`[1,2,3,4] → [4,3,2,1]`) and is proven
//! correct **for concrete lengths over symbolic memory**: both wasm ⊑ rev_loop
//! (the new refinement link) and wasm = `rev` (end to end) for n = 1..5, by pure
//! computation. Universal-`n` needs a simulation invariant (a relation between VM
//! state and the abstract `rev_loop` state, preserved per source iteration) — the
//! open next step, the analogue of M3's per-position invariant one level down.
//!
//! Design (see the discussion in the session / `ROADMAP.md` M4):
//! - The object language bans mutual recursion and demands structural recursion,
//!   so the textbook `exec_instr`/`exec_seq` pair is out. Instead a single
//!   non-recursive `step` does one machine step, and `run(cfg, fuel)` drives it,
//!   recursing structurally on `fuel`.
//! - Linear memory IS our `Mem`, so `ILoad`/`IStore` unfold to `read`/`write` and
//!   the whole M3 framing toolkit applies; the chain to `rev_loop` is direct.
//! - Structured control flow (`block`/`loop`/`br`/`br_if`) is modelled with an
//!   explicit control stack of `Frame`s. Each frame carries the code remaining in
//!   it and, for a loop, the `restart` body to re-enter on a back-branch — the one
//!   field that distinguishes loop (jump back) from block (jump forward/out).

use super::*;
// `simp` aliased: `super::*` already brings the proof-step builder `simp(side)`.
use proving_bootstrap::obj_lang::reduce::{eval, simp as reduce_simp};

// --- Rust-side builders for the wasm instruction/code data ------------------

fn iconst(n: Expr) -> Expr {
    ctor("IConst", vec![n])
}
fn iget(k: u64) -> Expr {
    ctor("IGet", vec![nat(k)])
}
fn iset(k: u64) -> Expr {
    ctor("ISet", vec![nat(k)])
}
fn iadd() -> Expr {
    ctor("IAdd", vec![])
}
fn isub() -> Expr {
    ctor("ISub", vec![])
}
fn ige() -> Expr {
    ctor("IGe", vec![])
}
fn iload() -> Expr {
    ctor("ILoad", vec![])
}
fn istore() -> Expr {
    ctor("IStore", vec![])
}
fn iblock(body: Expr) -> Expr {
    ctor("IBlock", vec![body])
}
fn iloop(body: Expr) -> Expr {
    ctor("ILoop", vec![body])
}
fn ibr(k: u64) -> Expr {
    ctor("IBr", vec![nat(k)])
}
fn ibrif(k: u64) -> Expr {
    ctor("IBrIf", vec![nat(k)])
}
/// A `Code` literal (monomorphic list of `Instr`): `CCons(.., CCons(.., CNil))`.
fn code(items: Vec<Expr>) -> Expr {
    items.into_iter().rev().fold(ctor("CNil", vec![]), |t, h| ctor("CCons", vec![h, t]))
}

// --- step helpers, as object-language expressions ---------------------------

/// Rebuild a `Config` from its four fields.
fn cfgx(vs: Expr, ls: Expr, mem: Expr, ctrl: Expr) -> Expr {
    ctor("Cfg", vec![vs, ls, mem, ctrl])
}

/// The current control stack with the *current* frame advanced past the
/// instruction just consumed: `KCons(Frm(isLoop, more, restart), rest)`. Valid
/// only inside `step`'s `CCons(instr, more)` arm, where these vars are bound.
fn adv() -> Expr {
    ctor("KCons", vec![ctor("Frm", vec![var("isLoop"), var("more"), var("restart")]), var("rest")])
}

/// A binary stack op: pop `b` (top) and `a` (next), push `result` (written in
/// terms of `a`, `b`). Stuck (returns `cfg` unchanged) if the stack is too short.
fn binop(result: Expr) -> Expr {
    match_(
        var("vs"),
        vec![
            arm(
                "Cons",
                &["b", "vs1"],
                match_(
                    var("vs1"),
                    vec![
                        arm("Cons", &["a", "vs2"], cfgx(cons(result, var("vs2")), var("ls"), var("mem"), adv())),
                        arm("Nil", &[], var("cfg")),
                    ],
                ),
            ),
            arm("Nil", &[], var("cfg")),
        ],
    )
}

/// The body of `step`: one machine step, dispatching on the head instruction of
/// the top control frame. Non-recursive (calls only the helpers + model fns).
fn step_body() -> Expr {
    let instr_dispatch = match_(
        var("instr"),
        vec![
            arm("IConst", &["n"], cfgx(cons(var("n"), var("vs")), var("ls"), var("mem"), adv())),
            arm("IGet", &["k"], cfgx(cons(call("nth", vec![var("ls"), var("k")]), var("vs")), var("ls"), var("mem"), adv())),
            arm(
                "ISet",
                &["k"],
                match_(
                    var("vs"),
                    vec![
                        arm("Cons", &["v", "vs1"], cfgx(var("vs1"), call("set_nth", vec![var("ls"), var("k"), var("v")]), var("mem"), adv())),
                        arm("Nil", &[], var("cfg")),
                    ],
                ),
            ),
            arm("IAdd", &[], binop(call("add", vec![var("a"), var("b")]))),
            arm("ISub", &[], binop(call("sub", vec![var("a"), var("b")]))),
            arm("ILt", &[], binop(call("b2n", vec![call("lt", vec![var("a"), var("b")])]))),
            // a >= b  ⟺  b <= a
            arm("IGe", &[], binop(call("b2n", vec![call("le", vec![var("b"), var("a")])]))),
            arm(
                "ILoad",
                &[],
                match_(
                    var("vs"),
                    vec![
                        arm("Cons", &["addr", "vs1"], cfgx(cons(call("read", vec![var("mem"), var("addr")]), var("vs1")), var("ls"), var("mem"), adv())),
                        arm("Nil", &[], var("cfg")),
                    ],
                ),
            ),
            arm(
                "IStore",
                &[],
                match_(
                    var("vs"),
                    vec![
                        arm(
                            "Cons",
                            &["v", "vs1"],
                            match_(
                                var("vs1"),
                                vec![
                                    arm("Cons", &["addr", "vs2"], cfgx(var("vs2"), var("ls"), call("write", vec![var("mem"), var("addr"), var("v")]), adv())),
                                    arm("Nil", &[], var("cfg")),
                                ],
                            ),
                        ),
                        arm("Nil", &[], var("cfg")),
                    ],
                ),
            ),
            // Enter a block: push a frame whose code is the block body; on exit
            // (br to it, or falling off its end) control resumes in `adv()`.
            arm("IBlock", &["body"], cfgx(var("vs"), var("ls"), var("mem"), ctor("KCons", vec![ctor("Frm", vec![fls(), var("body"), ctor("CNil", vec![])]), adv()]))),
            // Enter a loop: restart = the body, so a back-branch re-enters it.
            arm("ILoop", &["body"], cfgx(var("vs"), var("ls"), var("mem"), ctor("KCons", vec![ctor("Frm", vec![tru(), var("body"), var("body")]), adv()]))),
            arm("IBr", &["k"], cfgx(var("vs"), var("ls"), var("mem"), call("do_br", vec![adv(), var("k")]))),
            arm(
                "IBrIf",
                &["k"],
                match_(
                    var("vs"),
                    vec![
                        arm(
                            "Cons",
                            &["c", "vs1"],
                            match_(
                                var("c"),
                                vec![
                                    // 0 ⇒ not taken: fall through
                                    arm("Z", &[], cfgx(var("vs1"), var("ls"), var("mem"), adv())),
                                    // nonzero ⇒ taken: branch
                                    arm("S", &["_c"], cfgx(var("vs1"), var("ls"), var("mem"), call("do_br", vec![adv(), var("k")]))),
                                ],
                            ),
                        ),
                        arm("Nil", &[], var("cfg")),
                    ],
                ),
            ),
        ],
    );
    match_(
        var("cfg"),
        vec![arm(
            "Cfg",
            &["vs", "ls", "mem", "ctrl"],
            match_(
                var("ctrl"),
                vec![
                    arm("KNil", &[], var("cfg")), // halted: fixpoint
                    arm(
                        "KCons",
                        &["fr", "rest"],
                        match_(
                            var("fr"),
                            vec![arm(
                                "Frm",
                                &["isLoop", "code", "restart"],
                                match_(
                                    var("code"),
                                    vec![
                                        // frame fell off its end: pop it
                                        arm("CNil", &[], cfgx(var("vs"), var("ls"), var("mem"), var("rest"))),
                                        arm("CCons", &["instr", "more"], instr_dispatch),
                                    ],
                                ),
                            )],
                        ),
                    ),
                ],
            ),
        )],
    )
}

/// The reverse loop body, in wasm. Stack discipline noted inline; locals are
/// `[i, j, tmp]` at indices 0, 1, 2.
fn rev_loop_body() -> Expr {
    code(vec![
        // if i >= j, exit the block (label 1)
        iget(0),
        iget(1),
        ige(),
        ibrif(1),
        // tmp = mem[i]
        iget(0),
        iload(),
        iset(2),
        // mem[i] = mem[j]
        iget(0),
        iget(1),
        iload(),
        istore(),
        // mem[j] = tmp
        iget(1),
        iget(2),
        istore(),
        // i = i + 1
        iget(0),
        iconst(nat(1)),
        iadd(),
        iset(0),
        // j = j - 1
        iget(1),
        iconst(nat(1)),
        isub(),
        iset(1),
        // loop back (label 0)
        ibr(0),
    ])
}

/// `wasm_module()` = the M3 model extended with the VM types and functions.
pub fn wasm_module() -> Module {
    let mut m = module();
    m.types.push(TypeDef {
        name: "Instr".into(),
        ctors: vec![
            CtorDef { name: "IConst".into(), fields: vec!["Nat".into()] },
            CtorDef { name: "IGet".into(), fields: vec!["Nat".into()] },
            CtorDef { name: "ISet".into(), fields: vec!["Nat".into()] },
            CtorDef { name: "IAdd".into(), fields: vec![] },
            CtorDef { name: "ISub".into(), fields: vec![] },
            CtorDef { name: "ILt".into(), fields: vec![] },
            CtorDef { name: "IGe".into(), fields: vec![] },
            CtorDef { name: "ILoad".into(), fields: vec![] },
            CtorDef { name: "IStore".into(), fields: vec![] },
            CtorDef { name: "IBlock".into(), fields: vec!["Code".into()] },
            CtorDef { name: "ILoop".into(), fields: vec!["Code".into()] },
            CtorDef { name: "IBr".into(), fields: vec!["Nat".into()] },
            CtorDef { name: "IBrIf".into(), fields: vec!["Nat".into()] },
        ],
    });
    m.types.push(TypeDef {
        name: "Code".into(),
        ctors: vec![
            CtorDef { name: "CNil".into(), fields: vec![] },
            CtorDef { name: "CCons".into(), fields: vec!["Instr".into(), "Code".into()] },
        ],
    });
    m.types.push(TypeDef {
        name: "Frame".into(),
        ctors: vec![CtorDef { name: "Frm".into(), fields: vec!["Bool".into(), "Code".into(), "Code".into()] }],
    });
    m.types.push(TypeDef {
        name: "Ctrl".into(),
        ctors: vec![
            CtorDef { name: "KNil".into(), fields: vec![] },
            CtorDef { name: "KCons".into(), fields: vec!["Frame".into(), "Ctrl".into()] },
        ],
    });
    m.types.push(TypeDef {
        name: "Config".into(),
        ctors: vec![CtorDef { name: "Cfg".into(), fields: vec!["List".into(), "List".into(), "Mem".into(), "Ctrl".into()] }],
    });

    m.fns.push(fndef("b2n", vec![param("b", "Bool")], "Nat", match_(var("b"), vec![arm("True", &[], s(z())), arm("False", &[], z())])));
    // nth(xs, k): the k-th element of a Nat list (Z past the end).
    m.fns.push(fndef(
        "nth",
        vec![param("xs", "List"), param("k", "Nat")],
        "Nat",
        match_(
            var("xs"),
            vec![
                arm("Nil", &[], z()),
                arm("Cons", &["h", "t"], match_(var("k"), vec![arm("Z", &[], var("h")), arm("S", &["kp"], call("nth", vec![var("t"), var("kp")]))])),
            ],
        ),
    ));
    // set_nth(xs, k, v): xs with index k replaced by v (no-op past the end).
    m.fns.push(fndef(
        "set_nth",
        vec![param("xs", "List"), param("k", "Nat"), param("v", "Nat")],
        "List",
        match_(
            var("xs"),
            vec![
                arm("Nil", &[], nil()),
                arm(
                    "Cons",
                    &["h", "t"],
                    match_(
                        var("k"),
                        vec![arm("Z", &[], cons(var("v"), var("t"))), arm("S", &["kp"], cons(var("h"), call("set_nth", vec![var("t"), var("kp"), var("v")])))],
                    ),
                ),
            ],
        ),
    ));
    // do_br(ctrl, k): branch to the k-th enclosing label. Drop k inner frames;
    // on the target — Loop ⇒ re-enter (code := restart), Block ⇒ exit (pop it).
    m.fns.push(fndef(
        "do_br",
        vec![param("ctrl", "Ctrl"), param("k", "Nat")],
        "Ctrl",
        match_(
            var("ctrl"),
            vec![
                arm("KNil", &[], ctor("KNil", vec![])),
                arm(
                    "KCons",
                    &["fr", "rest"],
                    match_(
                        var("k"),
                        vec![
                            arm(
                                "Z",
                                &[],
                                match_(
                                    var("fr"),
                                    vec![arm(
                                        "Frm",
                                        &["isLoop", "code", "restart"],
                                        match_(
                                            var("isLoop"),
                                            vec![
                                                arm("True", &[], ctor("KCons", vec![ctor("Frm", vec![tru(), var("restart"), var("restart")]), var("rest")])),
                                                arm("False", &[], var("rest")),
                                            ],
                                        ),
                                    )],
                                ),
                            ),
                            arm("S", &["kp"], call("do_br", vec![var("rest"), var("kp")])),
                        ],
                    ),
                ),
            ],
        ),
    ));
    m.fns.push(fndef("cfg_mem", vec![param("cfg", "Config")], "Mem", match_(var("cfg"), vec![arm("Cfg", &["vs", "ls", "mem", "ctrl"], var("mem"))])));
    m.fns.push(fndef("step", vec![param("cfg", "Config")], "Config", step_body()));
    m.fns.push(fndef(
        "run",
        vec![param("cfg", "Config"), param("fuel", "Nat")],
        "Config",
        match_(var("fuel"), vec![arm("Z", &[], var("cfg")), arm("S", &["k"], call("run", vec![call("step", vec![var("cfg")]), var("k")]))]),
    ));
    // The reverse program: block { loop { <body> } }.
    m.fns.push(fndef("rev_prog", vec![], "Code", code(vec![iblock(code(vec![iloop(rev_loop_body())]))])));
    // init_cfg(m, n): empty stack, locals [0, n-1, 0], memory m, one frame
    // holding the whole program.
    m.fns.push(fndef(
        "init_cfg",
        vec![param("m", "Mem"), param("n", "Nat")],
        "Config",
        cfgx(
            nil(),
            cons(z(), cons(call("pred", vec![var("n")]), cons(z(), nil()))),
            var("m"),
            ctor("KCons", vec![ctor("Frm", vec![fls(), call("rev_prog", vec![]), ctor("CNil", vec![])]), ctor("KNil", vec![])]),
        ),
    ));
    m
}

/// Memory holding `(addr, val)` cells, innermost-last.
fn mcells(pairs: &[(u64, u64)]) -> Expr {
    pairs.iter().rev().fold(ctor("MNil", vec![]), |rest, &(a, v)| ctor("MCell", vec![nat(a), nat(v), rest]))
}

// ---------------------------------------------------------------------------
// QoL: an untrusted stepper + Config pretty-printer for authoring VM proofs.
//
// `step`/`run` produce deeply-nested `Cfg(...)` terms that are unreadable in the
// raw `Expr` Display. This renders one compactly — stack, locals, memory, and a
// control-stack summary — and steps the machine one micro-step at a time via
// `simp` (so it works on symbolic states too, the way the proof will see them).
// Used from the `#[ignore]`d trace tests below, run with `--nocapture`.
// ---------------------------------------------------------------------------

/// `S^k(Z)` → `k`; anything else renders via its `Expr` Display (symbolic leaf).
fn show_nat(e: &Expr) -> String {
    let mut k = 0u64;
    let mut cur = e;
    loop {
        match cur {
            Expr::Ctor { name, args } if name == "Z" && args.is_empty() => return k.to_string(),
            Expr::Ctor { name, args } if name == "S" && args.len() == 1 => {
                k += 1;
                cur = &args[0];
            }
            other => return format!("{other}"),
        }
    }
}

/// Walk a cons-list (`cons`/`nil` ctor names), returning the elements and any
/// non-nil tail (a symbolic variable, in the universal-`n` setting).
fn seq_items<'a>(mut e: &'a Expr, cons: &str, nil: &str) -> (Vec<&'a Expr>, Option<&'a Expr>) {
    let mut items = Vec::new();
    loop {
        match e {
            Expr::Ctor { name, args } if name == cons && args.len() == 2 => {
                items.push(&args[0]);
                e = &args[1];
            }
            Expr::Ctor { name, args } if name == nil && args.is_empty() => return (items, None),
            other => return (items, Some(other)),
        }
    }
}

/// Render the memory as `{a=v, ...}`, peeling both `MCell` ctors and `write`
/// calls (whichever `simp` left), down to `MNil` or a symbolic base.
fn show_mem(e: &Expr) -> String {
    let mut pairs = Vec::new();
    let mut cur = e;
    loop {
        match cur {
            Expr::Ctor { name, args } if name == "MCell" && args.len() == 3 => {
                pairs.push(format!("{}={}", show_nat(&args[0]), show_nat(&args[1])));
                cur = &args[2];
            }
            Expr::Call { name, args } if name == "write" && args.len() == 3 => {
                pairs.push(format!("{}={}", show_nat(&args[1]), show_nat(&args[2])));
                cur = &args[0];
            }
            Expr::Ctor { name, args } if name == "MNil" && args.is_empty() => return format!("{{{}}}", pairs.join(", ")),
            other => return format!("{{{} | {other}}}", pairs.join(", ")),
        }
    }
}

/// Control-stack summary: each frame as `loop(+N:HEAD)` / `block(+N:HEAD)`, where
/// N is the instructions remaining in the frame and HEAD is the next one.
fn show_ctrl(e: &Expr) -> String {
    let (frames, _) = seq_items(e, "KCons", "KNil");
    let rendered: Vec<String> = frames
        .iter()
        .map(|fr| match fr {
            Expr::Ctor { name, args } if name == "Frm" && args.len() == 3 => {
                let kind = match &args[0] {
                    Expr::Ctor { name, .. } if name == "True" => "loop",
                    _ => "block",
                };
                let (instrs, _) = seq_items(&args[1], "CCons", "CNil");
                let head = instrs.first().and_then(|i| if let Expr::Ctor { name, .. } = i { Some(name.as_str()) } else { None }).unwrap_or("-");
                format!("{kind}(+{}:{head})", instrs.len())
            }
            other => format!("{other}"),
        })
        .collect();
    format!("[{}]", rendered.join(", "))
}

/// One-line view of a `Cfg(stack, locals, mem, ctrl)` term.
fn show_cfg(cfg: &Expr) -> String {
    if let Expr::Ctor { name, args } = cfg
        && name == "Cfg"
        && args.len() == 4
    {
        let (stack, _) = seq_items(&args[0], "Cons", "Nil");
        let stack: Vec<String> = stack.iter().map(|e| show_nat(e)).collect();
        let (locals, _) = seq_items(&args[1], "Cons", "Nil");
        let labels = ["i", "j", "tmp"];
        let locals: Vec<String> = locals
            .iter()
            .enumerate()
            .map(|(k, e)| format!("{}={}", labels.get(k).copied().unwrap_or("?"), show_nat(e)))
            .collect();
        format!("stack=[{}] locals=[{}] mem={} ctrl={}", stack.join(","), locals.join(" "), show_mem(&args[2]), show_ctrl(&args[3]))
    } else {
        format!("{cfg}")
    }
}

/// One machine step, by `simp`-reducing `step(cfg)`. Works on symbolic states.
fn vm_step(m: &Module, cfg: &Expr) -> Expr {
    reduce_simp(m, &call("step", vec![cfg.clone()]))
}

/// Print `n` steps of the VM from `cfg0`, one config per line. Returns the final
/// config so a caller can assert on it.
fn vm_trace(m: &Module, cfg0: Expr, n: usize) -> Expr {
    let mut cur = cfg0;
    println!("  0: {}", show_cfg(&cur));
    for i in 1..=n {
        cur = vm_step(m, &cur);
        println!("{i:>3}: {}", show_cfg(&cur));
        // stop early once halted (empty control stack)
        if let Expr::Ctor { name, args } = &cur
            && name == "Cfg"
            && matches!(&args[3], Expr::Ctor { name, .. } if name == "KNil")
        {
            println!("     (halted after {i} steps)");
            break;
        }
    }
    cur
}

#[test]
#[ignore = "authoring aid: prints the VM trace of the n=4 reverse (run with --nocapture)"]
fn trace_wasm_reverse_n4() {
    let m = wasm_module();
    let mem0 = mcells(&[(0, 1), (1, 2), (2, 3), (3, 4)]);
    let cfg0 = reduce_simp(&m, &call("init_cfg", vec![mem0, nat(4)]));
    vm_trace(&m, cfg0, 80);
}

#[test]
#[ignore = "authoring aid: VM trace with symbolic memory (what the proof sees)"]
fn trace_wasm_reverse_symbolic() {
    // Concrete length so control flow unfolds, but symbolic memory `m` — exactly
    // the shape the correctness proof reasons about. Shows the read/write tower.
    let m = wasm_module();
    let cfg0 = reduce_simp(&m, &call("init_cfg", vec![var("m"), nat(4)]));
    vm_trace(&m, cfg0, 80);
}

#[test]
fn wasm_module_is_admitted() {
    assert_eq!(check_module(&wasm_module()), Ok(()));
}

#[test]
fn wasm_reverse_executes() {
    let m = wasm_module();
    // Memory [1, 2, 3, 4] at addresses 0..3; run the wasm reverse; read back.
    let mem0 = mcells(&[(0, 1), (1, 2), (2, 3), (3, 4)]);
    let final_list = call(
        "arr_from",
        vec![call("cfg_mem", vec![call("run", vec![call("init_cfg", vec![mem0, nat(4)]), nat(80)])]), z(), nat(4)],
    );
    let got = eval(&m, &final_list).expect("wasm reverse evaluates");
    assert_eq!(got, list(vec![nat(4), nat(3), nat(2), nat(1)]), "wasm reverse should produce [4,3,2,1]");
}

/// The list read back from the wasm reverse of an `n`-element buffer in symbolic
/// memory `m`, after `fuel` steps: `arr_from(cfg_mem(run(init_cfg(m,n), fuel)), 0, n)`.
fn wasm_result_list(n: u64, fuel: u64) -> Expr {
    call(
        "arr_from",
        vec![call("cfg_mem", vec![call("run", vec![call("init_cfg", vec![var("m"), nat(n)]), nat(fuel)])]), z(), nat(n)],
    )
}

/// wasm-reverse ⊑ rev_loop, for a concrete length, over *symbolic* memory. With
/// `n` concrete, the VM's control flow (the `i≥j` tests on concrete locals)
/// unfolds completely; only the memory values stay symbolic. So both sides reduce
/// under `simp` to the same tower of `read`/`write` over `m` — the proof is pure
/// computation, no simulation invariant yet. This is the new refinement link.
fn wasm_refines_rev_loop_fixed(n: u64, fuel: u64) -> Theorem {
    theorem(
        "wasm_refines_rev_loop_fixed",
        forall_eq(
            vec![param("m", "Mem")],
            wasm_result_list(n, fuel),
            call("arr_from", vec![call("rev_loop", vec![var("m"), z(), nat(n - 1)]), z(), nat(n)]),
        ),
        steps(vec![simp(Side::Both)], refl()),
    )
}

/// wasm-reverse = functional `rev`, end to end, for a concrete length over
/// symbolic memory — the M3 capstone reached from actual wasm bytecode.
fn wasm_reverse_eq_rev_fixed(n: u64, fuel: u64) -> Theorem {
    theorem(
        "wasm_reverse_eq_rev_fixed",
        forall_eq(
            vec![param("m", "Mem")],
            wasm_result_list(n, fuel),
            call("rev", vec![call("arr_from", vec![var("m"), z(), nat(n)])]),
        ),
        steps(vec![simp(Side::Both)], refl()),
    )
}

#[test]
fn wasm_refines_rev_loop_for_fixed_sizes() {
    let m = wasm_module();
    // fuel: ~13 steps per swap iteration plus block/loop entry and exit; 80 is
    // comfortably past the halt point for n ≤ 4 (extra fuel is a no-op fixpoint).
    for n in 1..=5 {
        assert_eq!(check_theorem(&m, &Theory::default(), &wasm_refines_rev_loop_fixed(n, 80)), Ok(()), "n = {n}");
    }
}

#[test]
fn wasm_reverse_equals_rev_for_fixed_sizes() {
    let m = wasm_module();
    for n in 1..=5 {
        assert_eq!(check_theorem(&m, &Theory::default(), &wasm_reverse_eq_rev_fixed(n, 80)), Ok(()), "n = {n}");
    }
}
