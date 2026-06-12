use std::time::{Duration, Instant};

use egg::rewrite as rw;
use egg::*;

type EGraph = egg::EGraph<HardwareLanguage, BVAnalysis>;
type Rewrite = egg::Rewrite<HardwareLanguage, BVAnalysis>;
type Runner = egg::Runner<HardwareLanguage, BVAnalysis>;

define_language! {
    enum HardwareLanguage {

        "Cons" = Cons([Id; 2]),
        "Head" = Head([Id; 1]),
        "Tail" = Tail([Id; 1]),
        // Arithmetic operations also take an output width
        "+" = Add([Id; 3]),
        "-" = Sub([Id; 3]),
        "*" = Mul([Id; 3]),
        "XOR" = Xor([Id; 3]),
        "<<" = ShiftLeft([Id; 3]),
        "~" = Not([Id; 2]),
        "SEL" = Sel([Id; 4]),
        "extract" = Extract([Id; 3]),
        // Bitvector Def: (bv 16 y)
        "bv" = BitVec([Id; 2]),
        // Basic Types
        Num(i64),
        Symbol(Symbol),
    }
}

//----------------------------------------------------------------------------//
// Analysis - performing constant folding
//----------------------------------------------------------------------------//
#[derive(Debug, Clone)]
struct BVData {
    constant: Option<(i64, PatternAst<HardwareLanguage>)>, // For constant folding
}

#[derive(Default)]
pub struct BVAnalysis;
impl Analysis<HardwareLanguage> for BVAnalysis {
    type Data = BVData;

    fn make(egraph: &mut EGraph, enode: &HardwareLanguage) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|d| d.0);
        let constant = match enode {
            HardwareLanguage::Num(c) => Some((*c, format!("{}", c).parse().unwrap())),
            HardwareLanguage::Add([w, a, b]) => {
                if let (Some(cw), Some(c1), Some(c2)) = (x(w), x(a), x(b)) {
                    Some((
                        (c1 + c2) % (1 << cw),
                        format!("(+ {cw} {c1} {c2})").parse().unwrap(),
                    ))
                } else {
                    None
                }
            }
            HardwareLanguage::Sub([w, a, b]) => {
                if let (Some(cw), Some(c1), Some(c2)) = (x(w), x(a), x(b)) {
                    Some((
                        (c1 - c2) % (1 << cw),
                        format!("(- {cw} {c1} {c2})").parse().unwrap(),
                    ))
                } else {
                    None
                }
            }
            HardwareLanguage::Mul([w, a, b]) => {
                if let (Some(cw), Some(c1), Some(c2)) = (x(w), x(a), x(b)) {
                    Some((
                        (c1 * c2) % (1 << cw),
                        format!("(* {cw} {c1} {c2})").parse().unwrap(),
                    ))
                } else {
                    None
                }
            }
            HardwareLanguage::ShiftLeft([w, a, b]) => {
                if let (Some(cw), Some(c1), Some(c2)) = (x(w), x(a), x(b)) {
                    Some((
                        (c1 << c2) % (1 << cw),
                        format!("(<< {cw} {c1} {c2})").parse().unwrap(),
                    ))
                } else {
                    None
                }
            }
            HardwareLanguage::Extract([w, from, expr]) => {
                if let (Some(cw), Some(cfrom), Some(cexpr)) = (x(w), x(from), x(expr)) {
                    let mask = (1 << (cw as i64)) - 1;
                    Some((
                        (cexpr >> cfrom) & mask,
                        format!("(extract {cw} {cfrom} {cexpr})").parse().unwrap(),
                    ))
                } else {
                    None
                }
            }
            _ => None,
        };

        BVData { constant: constant }
    }

    // Need to call merge across definitions
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let merge = merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        });
        merge
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();

        if let Some((c, pat)) = data.constant {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(HardwareLanguage::Num(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

//----------------------------------------------------------------------------//
// Rewrites
//----------------------------------------------------------------------------//
fn make_rules() -> Vec<Rewrite> {
    vec![
        // ARITHMETIC
        rw!("add-comm"; "(+ ?w ?a ?b)" => "(+ ?w ?b ?a)"),
        rw!("add-assoc"; "(+ ?w ?a (+ ?w ?b ?c))" => "(+ ?w (+ ?w ?a ?b) ?c)"),
        rw!("mul-comm"; "(* ?w ?a ?b)" => "(* ?w ?b ?a)"),
        rw!("xor-comm"; "(XOR ?w ?a ?b)" => "(XOR ?w ?b ?a)"),
        rw!("undistribute-left"; "(+ ?w (* ?w ?a ?b) (* ?w ?a ?c))" => "(* ?w ?a (+ ?w ?b ?c))"),
        rw!("undistribute-right"; "(+ ?w (* ?w ?a ?b) (* ?w ?c ?b))" => "(* ?w (+ ?w ?a ?c) ?b)"),
        rw!("sub-same"; "(- ?w ?a ?a)" => "0"),
        rw!("add-zero"; "(+ ?w ?a 0)" => "?a"),
        rw!("assoc-add-sub"; "(- ?w (+ ?w ?a ?b) ?c)" => "(+ ?w (- ?w ?a ?c) ?b)"),
        rw!("distribute-mult"; "(* ?w ?a (+ ?w ?b ?c))" => "(+ ?w (* ?w ?a ?b) (* ?w ?a ?c))"),
        rw!("add-bit"; "(+ 1 ?a ?b)" => "(XOR 1 ?a ?b)"),
        rw!("sel-xor"; "(SEL 1 ?s (~ 1 ?a) ?a)" => "(XOR 1 ?s ?a)"),
        // LOGICAL SHIFT
        rw!("shift-mul-1"; "(<< ?w (* ?w ?a ?b) ?s)" => "(* ?w ?a (<< ?w ?b ?s))"),
        // rw!("shift-mul-2"; "(* ?w ?a (<< ?w ?b ?s))" => "(* ?w (<< ?w ?a ?s) ?b)"),
        rw!("shift-add"; "(<< ?w (+ ?w ?a ?b) ?s)" => "(+ ?w (<< ?w ?a ?s) (<< ?w ?b ?s))"),
        rw!("undist-shift"; "(+ ?w (<< ?w ?a ?sa) (<< ?w ?b ?sb))" => "(<< ?w (+ ?w (<< ?w ?a (- 16 ?sa ?sb)) ?b) ?sb)" if a_gt_b("?sa", "?sb")),
        // BITVECTOR
        rw!("add-to-extract"; "(+ ?w (<< ?w (extract ?w_high ?from ?x) ?from) (extract ?from 0 ?x))" => "(extract (+ 16 ?w_high ?from) 0 ?x)"),
        rw!("extract-of-bv"; "(extract ?w 0 (bv ?w ?x))" => "(bv ?w ?x)"),
        rw!("extract-of-add"; "(extract ?w 0 (+ ?w1 ?a ?b))" => "(+ ?w (extract ?w 0 ?a) (extract ?w 0 ?b))" if a_gt_b("?w1", "?w")),
        // Cons rewrites
        rw!("add-cons"; "(+ ?w (Cons ?ah ?at) (Cons ?bh ?bt))" => "(Cons (+ ?w ?ah ?bh) (+ ?w ?at ?bt))"),
        rw!("sub-cons"; "(- ?w (Cons ?ah ?at) (Cons ?bh ?bt))" => "(Cons (- ?w ?ah ?bh) (- ?w ?at ?bt))"),
        rw!("mul-cons"; "(* ?w (Cons ?ah ?at) (Cons ?bh ?bt))" => "(Cons (* ?w ?ah ?bh) (* ?w ?at ?bt))"),
        rw!("extract-cons"; "(extract ?w ?from (Cons ?ah ?at))" => "(Cons (extract ?w ?from ?ah) (extract ?w ?from ?at))"),
        rw!("shift-cons"; "(<< ?w (Cons ?ah ?at) ?b)" => "(Cons (<< ?w ?ah (Head ?b)) (<< ?w ?at (Tail ?b)))"),
        rw!("head-const"; "(Head ?a)" => "?a" if is_const("?a")),
        rw!("tail-const"; "(Tail ?a)" => "?a" if is_const("?a")),
    ]
}

// This returns a function that implements Condition
fn is_const(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    // note this check is just an example,
    // checking for the absence of 0 is insufficient since 0 could be merged in later
    // see https://github.com/egraphs-good/egg/issues/297
    move |egraph, _, subst| {
        let id = subst[var];
        egraph[id].data.constant.is_some()
    }
}

// This returns a function that implements Condition
fn a_gt_b(a: &'static str, b: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var_a = a.parse().unwrap();
    let var_b = b.parse().unwrap();
    // note this check is just an example,
    // checking for the absence of 0 is insufficient since 0 could be merged in later
    // see https://github.com/egraphs-good/egg/issues/297
    move |egraph, _, subst| {
        let id_a = subst[var_a];
        let id_b = subst[var_b];
        if egraph[id_a].data.constant.is_none() || egraph[id_b].data.constant.is_none() {
            return false;
        }

        let a_const = egraph[id_a].data.constant.clone().unwrap().0;
        let b_const = egraph[id_b].data.constant.clone().unwrap().0;
        a_const > b_const
    }
}

//----------------------------------------------------------------------------//
// Testing
//----------------------------------------------------------------------------//

#[test]
fn parity() {
    let runner = Runner::default()
        .with_explanations_enabled()
        .with_definition(
            &"outSpec".parse().unwrap(),
            &"(Cons 0 (SEL 1 (bv 1 bitIn) (~ 1 outSpec) outSpec))"
                .parse()
                .unwrap(), // &"(Cons 0 (XOR 1 (bv 1 bitIn) outSpec))".parse().unwrap(),
        )
        .with_definition(
            &"count".parse().unwrap(),
            &"(Cons 0 (+ 8 count (bv 1 bitIn)))".parse().unwrap(),
        )
        .with_definition(
            &"outImpl".parse().unwrap(),
            &"(extract 1 0 count)".parse().unwrap(),
        )
        .disable_definition_rebuilding()
        .with_iter_limit(7)
        .run(&make_rules());

    runner.egraph.dot().to_dot("dots/parity.dot").unwrap();
    runner.print_report();

    let spec = runner.defs[0];
    let imp = runner.defs[2];
    assert!(runner.egraph.check_bisimilar(spec, imp));
}

#[test]
fn basic_rewriting() {
    let runner = Runner::default()
        .with_expr(
            &"(+ 16 (<< 16 (extract 8 8 (bv 16 x)) 8) (extract 8 0 (bv 16 x)))"
                .parse()
                .unwrap(),
        )
        .with_expr(&"(bv 16 x)".parse().unwrap())
        .run(&make_rules());

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[test]
fn karatsuba_combinational_16bit() {
    let xh = "(extract 8 8 (bv 16 x))".to_string();
    let xl = "(extract 8 0 (bv 16 x))".to_string();
    let yh = "(extract 8 8 (bv 16 y))".to_string();
    let yl = "(extract 8 0 (bv 16 y))".to_string();

    let xhyh = format!("(* 32 {xh} {yh})");
    let xlyl = format!("(* 32 {xl} {yl})");
    let xhyl = format!("(* 32 {xh} {yl})");
    let xlyh = format!("(* 32 {xl} {yh})");
    let xhyl_plus_xlyh = format!("(+ 32 {xhyl} {xlyh})");
    let res = format!("(+ 32 (+ 32 (<< 32 {xhyh} 16) (<< 32 {xhyl_plus_xlyh} 8)) {xlyl})");

    let runner = Runner::default()
        .with_expr(&res.parse().unwrap())
        // .with_expr(&spec.parse().unwrap())
        .with_expr(&"(* 32 (bv 16 x) (bv 16 y))".parse().unwrap())
        .disable_definition_rebuilding()
        .run(&make_rules());

    // runner.egraph.dot().to_dot("dots/karasuba.dot");
    runner.print_report();
    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[test]
fn karatsuba_sequential_16bit() {
    let xh = "(extract 8 8 (bv 16 x))".to_string();
    let xl = "(extract 8 0 (bv 16 x))".to_string();
    let yh = "(extract 8 8 (bv 16 y))".to_string();
    let yl = "(extract 8 0 (bv 16 y))".to_string();

    let xhyh = format!("(* 32 {xh} {yh})");
    let xlyl = format!("(* 32 {xl} {yl})");
    let xhyl = format!("(* 32 {xh} {yl})");
    let xlyh = format!("(* 32 {xl} {yh})");

    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_definition(
            &"s1".parse().unwrap(),
            &"(Cons 0 (* 32 (bv 16 x) (bv 16 y)))".parse().unwrap(),
        )
        .with_definition(&"s2".parse().unwrap(), &"(Cons 0 s1)".parse().unwrap())
        .with_definition(
            &"out_spec".parse().unwrap(),
            &"(Cons 0 s2)".parse().unwrap(),
        )
        .with_definition(
            &"i1_hh".parse().unwrap(),
            &format!("(Cons 0 {xhyh})").parse().unwrap(),
        )
        .with_definition(
            &"i1_ll".parse().unwrap(),
            &format!("(Cons 0 {xlyl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_hl".parse().unwrap(),
            &format!("(Cons 0 {xhyl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_lh".parse().unwrap(),
            &format!("(Cons 0 {xlyh})").parse().unwrap(),
        )
        .with_definition(
            &"i2_xhyl_plus_xlyh".parse().unwrap(),
            &format!("(Cons 0 (+ 32 i1_hl i1_lh))").parse().unwrap(),
        )
        .with_definition(
            &"i2_hh_plus_ll".parse().unwrap(),
            &format!("(Cons 0 (+ 32 (<< 32 i1_hh 16) i1_ll))")
                .parse()
                .unwrap(),
        )
        .with_definition(
            &"out_impl".parse().unwrap(),
            &"(Cons 0 (+ 32 i2_hh_plus_ll (<< 32 i2_xhyl_plus_xlyh 8)))"
                .parse()
                .unwrap(),
        );

    runner = runner.run(&make_rules());
    // runner.egraph.dot().to_dot("dots/karasuba.dot");
    runner.print_report();

    let out_spec = runner.defs[2];
    let out_impl = runner.defs[9];
    assert_eq!(runner.egraph.find(out_spec), runner.egraph.find(out_impl));
}

#[test]
fn karatsuba_full_combinational_16bit() {
    let xh = "(extract 8 8 (bv 16 x))".to_string();
    let xl = "(extract 8 0 (bv 16 x))".to_string();
    let yh = "(extract 8 8 (bv 16 y))".to_string();
    let yl = "(extract 8 0 (bv 16 y))".to_string();

    let xhyh = format!("(* 32 {xh} {yh})");
    let xlyl = format!("(* 32 {xl} {yl})");
    let xhyl = format!("(* 32 {xh} {yl})");
    let xlyh = format!("(* 32 {xl} {yh})");
    let _xhyl_plus_xlyh_spec = format!("(+ 32 {xhyl} {xlyh})");
    let xh_plus_xl = format!("(+ 32 {xh} {xl})");
    let yh_plus_yl = format!("(+ 32 {yh} {yl})");
    let xh_plus_xl_times_yh_plus_yl = format!("(* 32 {xh_plus_xl} {yh_plus_yl})");
    let xhyl_plus_xlyh = format!("(- 32 (- 32 {xh_plus_xl_times_yh_plus_yl} {xhyh}) {xlyl})");
    let res = format!("(+ 32 (+ 32 (<< 32 {xhyh} 16) (<< 32 {xhyl_plus_xlyh} 8)) {xlyl})");

    let runner = Runner::default()
        .with_expr(&res.parse().unwrap())
        // .with_expr(&xhyl_plus_xlyh_spec.parse().unwrap())
        .with_expr(&"(* 32 (bv 16 x) (bv 16 y))".parse().unwrap())
        .disable_definition_rebuilding()
        .with_iter_limit(9)
        .with_node_limit(300000)
        .with_time_limit(Duration::new(20, 0))
        .with_scheduler(egg::SimpleScheduler)
        .run(&make_rules());

    // runner.egraph.dot().to_dot("dots/karasuba.dot");
    runner.print_report();

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[test]
fn karatsuba_full_sequential_16bit() {
    let xh = "(extract 8 8 (bv 16 x))".to_string();
    let xl = "(extract 8 0 (bv 16 x))".to_string();
    let yh = "(extract 8 8 (bv 16 y))".to_string();
    let yl = "(extract 8 0 (bv 16 y))".to_string();

    let xhyh = format!("(* 32 {xh} {yh})");
    let xlyl = format!("(* 32 {xl} {yl})");
    let xhyl = format!("(* 32 {xh} {yl})");
    let xlyh = format!("(* 32 {xl} {yh})");
    let xh_plus_xl = format!("(+ 32 {xh} {xl})");
    let yh_plus_yl = format!("(+ 32 {yh} {yl})");

    let start = std::time::Instant::now();
    let runner = Runner::default()
        .with_iter_limit(11)
        .with_node_limit(1000000)
        .with_time_limit(Duration::new(1000, 0))
        .disable_definition_rebuilding()
        .with_scheduler(egg::SimpleScheduler)
        .with_definition(
            &"s1".parse().unwrap(),
            &"(Cons 0 (* 32 (bv 16 x) (bv 16 y)))".parse().unwrap(),
        )
        .with_definition(&"s2".parse().unwrap(), &"(Cons 0 s1)".parse().unwrap())
        .with_definition(
            &"out_spec".parse().unwrap(),
            &"(Cons 0 s2)".parse().unwrap(),
        )
        .with_definition(
            &"i1_hh".parse().unwrap(),
            &format!("(Cons 0 {xhyh})").parse().unwrap(),
        )
        .with_definition(
            &"i1_ll".parse().unwrap(),
            &format!("(Cons 0 {xlyl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_x".parse().unwrap(),
            &format!("(Cons 0 {xh_plus_xl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_y".parse().unwrap(),
            &format!("(Cons 0 {yh_plus_yl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_hl".parse().unwrap(),
            &format!("(Cons 0 {xhyl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_lh".parse().unwrap(),
            &format!("(Cons 0 {xlyh})").parse().unwrap(),
        )
        .with_definition(
            &"i2_xhyl_plus_xlyh".parse().unwrap(),
            &format!("(Cons 0 (- 32 (- 32 (* 32 i1_x i1_y) i1_hh) i1_ll))")
                .parse()
                .unwrap(),
        )
        .with_definition(
            &"i2_hh_plus_ll".parse().unwrap(),
            &format!("(Cons 0 (+ 32 (<< 32 i1_hh 16) i1_ll))")
                .parse()
                .unwrap(),
        )
        .with_definition(
            &"out_impl".parse().unwrap(),
            &"(Cons 0 (+ 32 i2_hh_plus_ll (<< 32 i2_xhyl_plus_xlyh 8)))"
                .parse()
                .unwrap(),
        )
        .run(&make_rules());

    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);
    runner.print_report();
    let bisim_start = Instant::now();

    let out_spec = runner.defs[2];
    let out_impl = runner.defs[11];
    let bisim = runner
        .egraph
        .check_bisimilar(runner.egraph.find(out_spec), runner.egraph.find(out_impl));
    println!("Bisimulation check time: {:?}", bisim_start.elapsed());
    assert!(bisim);
}

#[test]
fn karatsuba_intermediate_goal() {
    let xh = "(extract 8 8 (bv 16 x))".to_string();
    let xl = "(extract 8 0 (bv 16 x))".to_string();
    let yh = "(extract 8 8 (bv 16 y))".to_string();
    let yl = "(extract 8 0 (bv 16 y))".to_string();

    let xhyh = format!("(* 32 {xh} {yh})");
    let xlyl = format!("(* 32 {xl} {yl})");
    let xhyl = format!("(* 32 {xh} {yl})");
    let xlyh = format!("(* 32 {xl} {yh})");
    let xhyl_plus_xlyh_spec = format!("(+ 32 {xhyl} {xlyh})");
    let xh_plus_xl = format!("(+ 32 {xh} {xl})");
    let yh_plus_yl = format!("(+ 32 {yh} {yl})");
    let xh_plus_xl_times_yh_plus_yl = format!("(* 32 {xh_plus_xl} {yh_plus_yl})");
    let xhyl_plus_xlyh = format!("(- 32 (- 32 {xh_plus_xl_times_yh_plus_yl} {xhyh}) {xlyl})");

    let runner = Runner::default()
        .with_expr(&xhyl_plus_xlyh_spec.parse().unwrap())
        .with_expr(&xhyl_plus_xlyh.parse().unwrap())
        .disable_definition_rebuilding()
        .with_iter_limit(6)
        .with_scheduler(egg::SimpleScheduler)
        .run(&make_rules());

    runner.egraph.dot().to_dot("dots/karasuba.dot").unwrap();
    runner.print_report();

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[ignore]
#[test]
fn int1() {
    let xh = "(extract 8 8 (bv 16 x))".to_string();
    let xl = "(extract 8 0 (bv 16 x))".to_string();
    let yh = "(extract 8 8 (bv 16 y))".to_string();
    let yl = "(extract 8 0 (bv 16 y))".to_string();

    let xhyh = format!("(* 32 {xh} {yh})");
    let xlyl = format!("(* 32 {xl} {yl})");
    let xhyl = format!("(* 32 {xh} {yl})");
    let xlyh = format!("(* 32 {xl} {yh})");
    let xh_plus_xl = format!("(+ 32 {xh} {xl})");
    let yh_plus_yl = format!("(+ 32 {yh} {yl})");

    let rules = make_rules();
    println!("Rules: {}", rules.len());
    let runner = Runner::default()
        .with_iter_limit(13)
        .with_node_limit(1000000)
        .with_time_limit(Duration::new(20, 0))
        // .disable_definition_rebuilding()
        .with_scheduler(egg::SimpleScheduler)
        .with_definition(
            &"i1_hh".parse().unwrap(),
            &format!("(Cons 0 {xhyh})").parse().unwrap(),
        )
        .with_definition(
            &"i1_ll".parse().unwrap(),
            &format!("(Cons 0 {xlyl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_x".parse().unwrap(),
            &format!("(Cons 0 {xh_plus_xl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_y".parse().unwrap(),
            &format!("(Cons 0 {yh_plus_yl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_hl".parse().unwrap(),
            &format!("(Cons 0 {xhyl})").parse().unwrap(),
        )
        .with_definition(
            &"i1_lh".parse().unwrap(),
            &format!("(Cons 0 {xlyh})").parse().unwrap(),
        )
        .with_definition(
            &"i2_xhyl_plus_xlyh".parse().unwrap(),
            // &format!("(Cons 0 (- 32 (- 32 (* 32 i1_x i1_y) i1_hh) i1_ll))")
            &format!("(Cons 0 (+ 32 i1_hl i1_lh))").parse().unwrap(),
        )
        .with_expr(
            &"(Cons 0 (- 32 (- 32 (* 32 i1_x i1_y) i1_hh) i1_ll))"
                .parse()
                .unwrap(),
        )
        .with_expr(
            &format!(
                "(Cons 0 (Cons 0 (- 32 (- 32 (* 32 {xh_plus_xl} {yh_plus_yl}) {xhyh}) {xlyl})))"
            )
            .parse()
            .unwrap(),
        )
        .run(&make_rules());
    runner.print_report();

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}
