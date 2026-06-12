use egg::rewrite as rw;
use egg::*;
use std::collections::HashSet;

type EGraph = egg::EGraph<StreamLanguage, StreamsAnalysis>;
type Rewrite = egg::Rewrite<StreamLanguage, StreamsAnalysis>;
type Runner = egg::Runner<StreamLanguage, StreamsAnalysis>;

//----------------------------------------------------------------------------//
// Language - captures standard operations on streams
//----------------------------------------------------------------------------//
define_language! {
    enum StreamLanguage {
        Num(i32),
        "Cons" = Cons([Id; 2]),
        "Head" = Head([Id; 1]),
        "Tail" = Tail([Id; 1]),
        "Snd" = Snd([Id; 2]),
        "S" = Successor([Id; 1]),
        "Node" = Node([Id; 3]),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "<" = Lt([Id; 2]),
        "ite" = Ite([Id; 3]),
        "!=" = Neq([Id; 2]),
        "f" = F([Id; 1]),
        "g" = G([Id; 1]),
        "h" = H([Id; 1]),
        "Map" = Map([Id; 2]),
        "App" = App([Id; 2]),
        Symbol(Symbol),
    }
}

//----------------------------------------------------------------------------//
// Analysis - performing constant folding & unique elements of stream (sets)
//----------------------------------------------------------------------------//
#[derive(Debug, Clone)]
struct StreamsData {
    constant: Option<(i32, PatternAst<StreamLanguage>)>, // For constant folding
    elements: HashSet<i32>,                              // For stream elements
}

#[derive(Default)]
pub struct StreamsAnalysis;
impl Analysis<StreamLanguage> for StreamsAnalysis {
    type Data = StreamsData; // (Option<(i32, PatternAst<StreamLanguage>)>, HashSet<i32>);

    fn make(egraph: &mut EGraph, enode: &StreamLanguage) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|d| d.0);
        let constant = match enode {
            StreamLanguage::Num(c) => Some((*c, format!("{}", c).parse().unwrap())),
            StreamLanguage::Add([a, b]) => {
                if x(a).is_some() && x(b).is_some() {
                    Some((
                        x(a).unwrap() + x(b).unwrap(),
                        format!("(+ {} {})", x(a).unwrap(), x(b).unwrap())
                            .parse()
                            .unwrap(),
                    ))
                } else {
                    None
                }
            }
            StreamLanguage::Mul([a, b]) => {
                if x(a).is_some() && x(b).is_some() {
                    Some((
                        x(a).unwrap() * x(b).unwrap(),
                        format!("(* {} {})", x(a).unwrap(), x(b).unwrap())
                            .parse()
                            .unwrap(),
                    ))
                } else {
                    None
                }
            }
            StreamLanguage::Lt([a, b]) => {
                if x(a).is_some() && x(b).is_some() {
                    Some((
                        (x(a).unwrap() < x(b).unwrap()) as i32,
                        format!("(< {} {})", x(a).unwrap(), x(b).unwrap())
                            .parse()
                            .unwrap(),
                    ))
                } else {
                    None
                }
            }
            _ => None,
        };

        // How to construct the elements set
        let y = |i: &Id| &egraph[*i].data.elements;
        let mut set = HashSet::new();
        match enode {
            StreamLanguage::Num(c) => {
                set.insert(*c);
            }
            StreamLanguage::Cons(_) => {
                for child in enode.children() {
                    set.extend(y(child));
                }
            }
            StreamLanguage::Ite([a, b, c]) => {
                if y(a).contains(&1) {
                    set.extend(y(b));
                }
                if y(a).contains(&0) {
                    set.extend(y(c));
                }
            }
            _ => (),
        };
        StreamsData {
            constant: constant,
            elements: set,
        }
    }

    // Need to call merge across definitions
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let mut merge = merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        });

        // Define how to merge the element sets - this is a join
        let to_elts_orig = to.elements.len();
        to.elements.extend(&from.elements);

        // Identify whether the merge should propagate
        merge.0 |= to_elts_orig != to.elements.len();
        merge.1 |= from.elements.len() != to.elements.len();

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
                let added = egraph.add(StreamLanguage::Num(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            // #[cfg(debug_assertions)]
            // egraph[id].assert_unique_leaves();
        }

        // If elements returns a singleton set - we can fold into a constant stream
        // if data.elements.len() == 1 {
        //     let elt = *data.elements.iter().next().unwrap();
        //     let pat = format!("{}", elt).parse().unwrap();
        //     if egraph.are_explanations_enabled() {
        //         egraph.union_instantiations(
        //             &pat,
        //             &format!("{}", elt).parse().unwrap(),
        //             &Default::default(),
        //             "element_fold".to_string(),
        //         );
        //     } else {
        //         let added = egraph.add(StreamLanguage::Num(elt));
        //         egraph.union(id, added);
        //     }
        //     // to not prune, comment this out
        //     egraph[id].nodes.retain(|n| n.is_leaf());

        //     #[cfg(debug_assertions)]
        //     egraph[id].assert_unique_leaves();
        // }
    }
}

fn make_rules() -> Vec<Rewrite> {
    vec![
        // Basic arithmetic
        rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("distribute"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("add-two"; "(+ ?a ?a)" => "(* 2 ?a)"),
        rw!("add-zero"; "(+ ?a 0)" => "?a"),
        // Map and Applications
        rw!("propagate-map"; "(Map ?func (Cons ?a ?b))" => "(Cons (App ?func ?a) (Map ?func ?b))"),
        rw!("apply-incr"; "(App incr ?a)" => "(+ ?a 1)"),
        rw!("tail-cons"; "(Tail (Cons ?a ?b))" => "?b"),
        rw!("add-cons"; "(+ ?a (Cons ?b ?c))" => "(Cons (+ (Head ?a) ?b) (+ (Tail ?a) ?c))"),
        rw!("lt-cons-right"; "(< ?a (Cons ?b ?c))" => "(Cons (< (Head ?a) ?b) (< (Tail ?a) ?c))"),
        rw!("lt-cons-left"; "(< (Cons ?b ?c) ?a)" => "(Cons (< ?b (Head ?a)) (< ?c (Tail ?a)))"),
        rw!("lt-ite"; "(< (ite ?cond ?a ?b) ?c)" => "(ite ?cond (< ?a ?c) (< ?b ?c))"),
        // Constant streams
        rw!("head-const"; "(Head ?a)" => "?a" if is_const("?a")),
        rw!("tail-const"; "(Tail ?a)" => "?a" if is_const("?a")),
        rw!("neq-same"; "(!= ?a ?a)" => "false"),
        rw!("ite-false"; "(ite false ?a ?b)" => "?b"),
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

//----------------------------------------------------------------------------//
// Basic Functionalities
//----------------------------------------------------------------------------//
#[test]
#[should_panic]
fn circular_definition_detection() {
    // x := f(x)
    // y := y
    let mut egraph = EGraph::default();
    egraph.add_definition(&"x".parse().unwrap(), &"y".parse().unwrap());
    egraph.add_definition(&"y".parse().unwrap(), &"x".parse().unwrap());

    // Expect to fail
    egraph.rebuild();
}

#[test]
fn trees() {
    // From Wojtek's Slack Example
    let mut egraph = EGraph::default();

    let ids_a = egraph.add_definition(
        &"tree1".parse().unwrap(),
        &"(Node 1 tree1 tree1)".parse().unwrap(),
    );
    let ids_b = egraph.add_definition(
        &"tree2".parse().unwrap(),
        &"(Node 1 (Node 1 tree2 tree2) (Node 1 tree2 tree2))"
            .parse()
            .unwrap(),
    );
    egraph.rebuild();

    assert_eq!(egraph.find(ids_a.0), egraph.find(ids_b.0));
}

#[test]
fn idempotent_function() -> Result<(), std::io::Error> {
    // Check that e-graph equivalence loops (x+0->x) don't merge definitions
    // a := Cons(x, 2 + 0)
    // b := Cons(x, 1 + 0)
    let runner = Runner::default()
        .with_definition(&"a".parse().unwrap(), &"(f (+ a' 0))".parse().unwrap())
        .with_definition(&"b".parse().unwrap(), &"(f (+ b' 0))".parse().unwrap())
        .with_iter_limit(2)
        .run(&make_rules());
    runner.egraph.dot().automata_to_dot("dots/idempotent.dot")?;
    assert_ne!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );

    Ok(())
}

#[test]
fn ones() {
    // Basic example inspired by Cocaml
    let mut egraph = EGraph::default();
    let b = "b".parse().unwrap();
    let bstream = "(Cons 1 (Cons 1 b))".parse().unwrap();
    egraph.add_definition(&b, &bstream);
    egraph.rebuild();
    egraph.dot().to_dot("dots/test.dot").unwrap();
}

#[test]
fn merged_observations() {
    // Definitions
    // x := Cons(z, f(x))
    // y := Cons(z, w)
    // Equivalences
    // f(x) = g(x)
    // f(y) = w
    let mut egraph = EGraph::default();
    let x = egraph.add_definition(&"x".parse().unwrap(), &"(Cons z (f x))".parse().unwrap());
    let fx = egraph.add_expr(&"(f x)".parse().unwrap());
    let gx = egraph.add_expr(&"(g x)".parse().unwrap());
    egraph.union(fx, gx);

    let y = egraph.add_definition(&"y".parse().unwrap(), &"(Cons z w)".parse().unwrap());
    let fy = egraph.add_expr(&"(f y)".parse().unwrap());
    let h = egraph.add_expr(&"w".parse().unwrap());
    egraph.union(fy, h);
    egraph.rebuild();
    assert_eq!(egraph.find(x.0), egraph.find(y.0));
}

#[test]
fn needs_minimization() {
    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(Cons 0 (* 2 x))".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(Cons 0 (* 2 y))".parse().unwrap())
        .with_definition(&"z".parse().unwrap(), &"(Cons 0 (+ x y))".parse().unwrap());

    assert_ne!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[2])
    );
    assert_ne!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
    assert_ne!(
        runner.egraph.find(runner.roots[1]),
        runner.egraph.find(runner.roots[2])
    );

    runner.egraph.rebuild();
    assert_ne!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[2])
    );
    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
    assert_ne!(
        runner.egraph.find(runner.roots[1]),
        runner.egraph.find(runner.roots[2])
    );

    runner = runner.with_iter_limit(2).run(&make_rules());
    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[2])
    );
    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
    assert_eq!(
        runner.egraph.find(runner.roots[1]),
        runner.egraph.find(runner.roots[2])
    );
}
//----------------------------------------------------------------------------//
// SOURCE: CoCaml Paper
// CoCaml: Functional Programming with Regular Coinductive Types
//----------------------------------------------------------------------------//
#[test]
fn simple_ones() {
    // Basic example inspired by Cocaml
    let mut egraph = EGraph::default();
    let a = "a".parse().unwrap();
    let astream = "(Cons 1 a)".parse().unwrap();
    let ids_a = egraph.add_definition(&a, &astream);
    let b = "b".parse().unwrap();
    let bstream = "(Cons 1 (Cons 1 b))".parse().unwrap();
    let ids_b = egraph.add_definition(&b, &bstream);
    egraph.rebuild();
    // assert_eq!(egraph.find(ids_a.0), egraph.find(ids_b.0));
    assert!(egraph.check_bisimilar(ids_a.0, ids_b.0));
}

#[test]
fn cocaml_map() {
    // Cocaml example
    let mut runner = Runner::default()
        .with_definition(
            &"alt".parse().unwrap(),
            &"(Cons 1 (Cons 2 alt))".parse().unwrap(),
        )
        .with_expr(&"(Map incr alt)".parse().unwrap())
        .run(&make_rules());
    runner.egraph.dot().to_dot("dots/map.dot").unwrap();

    // Check (map alt) = 2 :: 3 :: (map alt)
    assert_eq!(
        runner
            .egraph
            .add_expr(&"(Cons 2 (Cons 3 (Map incr alt)))".parse().unwrap()),
        runner.egraph.find(runner.roots[1])
    );

    println!(
        "Alt Elements: {:?}",
        runner.egraph[runner.roots[1]].data.elements
    );
}

#[test]
fn cocaml_elements() {
    // Cocaml example of analysis
    let mut egraph = EGraph::default();
    let alt = egraph.add_definition(
        &"alt".parse().unwrap(),
        &"(Cons 1 (Cons 2 alt))".parse().unwrap(),
    );
    let ones = egraph.add_definition(&"ones".parse().unwrap(), &"(Cons 1 ones)".parse().unwrap());
    egraph.rebuild();

    // Check (map alt) = 2 :: 3 :: (map alt)
    assert_eq!(egraph[ones.1].data.elements, HashSet::from([1]));

    assert_eq!(egraph[alt.1].data.elements, HashSet::from([1, 2]));
}

//----------------------------------------------------------------------------//
// SOURCE: Phil Zucker's Blog
// commutative = https://www.philipzucker.com/coegraph/
// simple_dfa  = https://www.philipzucker.com/naive_automata/
//----------------------------------------------------------------------------//
#[test]
fn commutative() {
    // let mut egraph = EGraph::<StreamLanguage, ()>::default();
    // ab =: cons( (a + b) ab)
    // ba =: cons( (b + a) ba)
    let runner = Runner::default()
        .with_definition(
            &"ab".parse().unwrap(),
            &"(Cons (+ a b) ab)".parse().unwrap(),
        )
        .with_definition(
            &"ba".parse().unwrap(),
            &"(Cons (+ b a) ba)".parse().unwrap(),
        )
        .run(&make_rules());
    runner.egraph.dot().to_dot("dots/phil_example.dot").unwrap();
    assert!(runner
        .egraph
        .check_bisimilar(runner.roots[0], runner.roots[1]));
}

#[test]
fn simple_dfa() {
    let mut egraph = EGraph::default();

    egraph.add_definition(
        &"one".parse().unwrap(),
        &"(Node False two three)".parse().unwrap(),
    );
    let two = egraph.add_definition(
        &"two".parse().unwrap(),
        &"(Node False four three)".parse().unwrap(),
    );
    let three = egraph.add_definition(
        &"three".parse().unwrap(),
        &"(Node False five three)".parse().unwrap(),
    );
    let four = egraph.add_definition(
        &"four".parse().unwrap(),
        &"(Node True five four)".parse().unwrap(),
    );
    let five = egraph.add_definition(
        &"five".parse().unwrap(),
        &"(Node True four four)".parse().unwrap(),
    );

    egraph.rebuild();

    assert_eq!(egraph.find(two.0), egraph.find(three.0));
    assert_eq!(egraph.find(four.0), egraph.find(five.0));
}

// def myfun():
//     i = 1
//     j = 1
//     k = 0
//     while k < 100:
//         if j < 20:
//             j = i
//             k = k+1
//         else:
//             j = k
//             k = k + 2
//     return j
//
// i := cons(1, i)
// j := cons(1, if (j<20) then i else k)
// k := cons(0, if (j<20) then (k+1) else (k+2))

// (j<20) = cons(1, if (j<20) then i else k) < 20
//        = cons(1 < 20, if (j<20) then (i < 20) else (k < 20))
//        = cons(1, if (j<20) then 1 else (k<20))
// (i < 20) = cons(1<20, (i<20)) = cons(1, (i<20)) -> 1

// Why is the following true:
// x = cons(1, if x then 1 else k) => x = 1

#[test]
fn my_fun_zucker() -> Result<(), std::io::Error> {
    let runner = Runner::default()
        .with_definition(&"i".parse().unwrap(), &"(Cons 1 i)".parse().unwrap())
        .with_definition(
            &"j".parse().unwrap(),
            &"(Cons 1 (ite (< j 20) i k))".parse().unwrap(),
        )
        .with_expr(&"(< j 20)".parse().unwrap())
        .with_iter_limit(2)
        .run(&make_rules());
    runner.egraph.dot().to_dot("dots/my_fun_zucker.dot")?;

    let cond = runner.roots[2];
    println!("j elements: {:?}", runner.egraph[cond].data.elements);
    Ok(())
}
//----------------------------------------------------------------------------//
// SOURCE: SMT Paper
// A Decision Procedure for (Co)datatypes in SMT Solvers
// https://homepage.divms.uiowa.edu/~ajreynol/cade15.pdf
//----------------------------------------------------------------------------//
#[test]
fn smt_successor() {
    // Example taken from SMT paper Example 2 Section 3:
    // a := S(a)
    // b := S(S(b))
    let mut egraph = EGraph::default();
    let a = egraph.add_definition(&"a".parse().unwrap(), &"(S a)".parse().unwrap());
    let b = egraph.add_definition(&"b".parse().unwrap(), &"(S (S b))".parse().unwrap());
    egraph.rebuild();
    // assert_eq!(egraph.find(a.0), egraph.find(b.0));
    assert!(egraph.check_bisimilar(a.0, b.0));
}

//----------------------------------------------------------------------------//
// SOURCE: Berkeley Paper
// Optimism in Equality Saturation
// https://arxiv.org/abs/2511.20782
//----------------------------------------------------------------------------//
#[test]
// We are unable to resolve this case because our analyses are unaware of the definitional edges
// but also because we have no way of computing a fix-point of optimistic analyses
fn russel_fig_2() {
    // Figure 2(a) Example - Goal:  show that x \in {1+5z | z \in Nat}
    // x = 1;
    // while 1 {
    //      x = x + (1 * 5);
    // }
    // Represented as streams:
    // x := cons(1, x + (1 * 5))
    // elements(x) = elements(cons(1, x + (1*5))) = {1} ∪ elements(x + (1*5)) = {1} ∪ (elements(x) + elements(1*5))
    // x := cons(1, 5 + x)
    let mut egraph = EGraph::default();
    let _x = egraph.add_definition(
        &"x".parse().unwrap(),
        &"(Cons 1 (+ (* 1 5) x))".parse().unwrap(),
    );

    egraph.rebuild();
}

#[test]
fn russel_fig_6() -> Result<(), std::io::Error> {
    // Figure 6 Example - Goal: show that z == 42:
    // fn example1 ( y ) {
    //  let x = -6;
    //  let z = 42;
    //  while y < 10 {
    //      y = y + 1;
    //      x = x + 8;
    //      xt = x + 8;
    //      let lhs = (( xt + y ) + z ) * y ;
    //      let rhs = 2 * y + ( y * y + z * y ) ;
    //      if lhs ! = rhs {
    //          z = 24;
    //      }
    //      x = xt - 8;
    //  }
    //  return z + 7;
    // }
    // Represented as streams:
    // xt:= x+8 --> cons(-6+8, xt-8+8) --> cons(2, xt)
    // x := cons(-6, xt-8) --> cons(-6, x)
    // y := cons(y0, y+1)
    // lhs := (xt + y + z) * y
    // rhs := 2*y + (y*y + z*y)
    // z := cons(42, if lhs != rhs then 24 else z) --> cons(42, z)
    // Rewriting lhs != rhs --> xt*y != 2*y --> xt != 2 --> false
    let runner = Runner::default()
        .with_definition(&"xt".parse().unwrap(), &"(+ x 8)".parse().unwrap())
        .with_definition(&"x".parse().unwrap(), &"(Cons -6 x)".parse().unwrap())
        .with_definition(
            &"z".parse().unwrap(),
            &"(Cons 42 (ite (!= xt 2) 24 z))".parse().unwrap(),
        )
        .with_definition(&"target".parse().unwrap(), &"(Cons 42 z)".parse().unwrap())
        .run(&make_rules());
    // runner.egraph.rebuild();
    runner.egraph.dot().to_dot("dots/russel_fig_6.dot")?;

    assert_eq!(
        runner.egraph.find(runner.roots[2]),
        runner.egraph.find(runner.roots[3])
    );
    Ok(())
}

#[test]
fn russel_fig_7() -> Result<(), std::io::Error> {
    // Figure 7 Example - Goal: show that x==y
    // fn example2 (x) {
    // let y = x ;
    // while y < 10 {
    //      let xt = x ;
    //      x = y * y + y * 5;
    //      y = xt * ( y + 5 + 0) ;
    // }
    //  return x - y;
    // }

    // Represented as streams:
    // x := cons(x0, y*y + y*5)
    // xt := x
    // y := cons(x0, xt*(y + 5 + 0)) --> rewriting -->  cons(x0, x * y + x * 5)
    let runner = Runner::default()
        .with_definition(
            &"x".parse().unwrap(),
            &"(Cons x0 (+ (* y y) (* y 5)))".parse().unwrap(),
        )
        .with_definition(&"xt".parse().unwrap(), &"x".parse().unwrap())
        .with_definition(
            &"y".parse().unwrap(),
            &"(Cons x0 (* xt (+ y (+ 5 0))))".parse().unwrap(),
        )
        .run(&make_rules());
    // egraph.dot().automata_to_dot("dots/russel_fig_7.dot");

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[2])
    );
    Ok(())
}

//----------------------------------------------------------------------------//
// SOURCE: Cheng's Examples (Slack and Working Document)
//----------------------------------------------------------------------------//
#[should_panic]
#[test]
fn chengs_example_circular() {
    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"x".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(f z)".parse().unwrap())
        .with_definition(&"z".parse().unwrap(), &"(f y)".parse().unwrap());
    runner.egraph.rebuild();

    let rules: Vec<Rewrite> = vec![rw!(
        "f-x";
        "x" => "(f x)"
    )];
    runner = runner.with_iter_limit(2).run(&rules);

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[test]
fn chengs_example_3_5_1() {
    // x := f(x)
    // y := f(f(x))
    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(f x)".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(f (f x))".parse().unwrap());
    runner.egraph.rebuild();

    assert!(runner
        .egraph
        .check_bisimilar(runner.roots[0], runner.roots[1]));
}

#[test]
#[should_panic]
fn chengs_example_3_5_2() {
    // x := f(x)
    // y := y
    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(f x)".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"y".parse().unwrap());

    // Circular definition asserts
    runner.egraph.rebuild();
}

#[test]
#[should_panic]
fn chengs_example_3_6() {
    // x := g(x)
    // y := g(y)
    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(g x)".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(g y)".parse().unwrap());

    runner.egraph.rebuild();
    let rules: Vec<Rewrite> = vec![rw!(
        "g-y";
        "(g y)" => "y"
    )];
    runner = runner.with_iter_limit(1).run(&rules);
    runner.egraph.rebuild(); // Expected to fail
}

#[test]
fn chengs_example_3_7() {
    // x := cons(x, f(y))
    // y := cons(y, f(x))

    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(Cons x (f y))".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(Cons y (g x))".parse().unwrap());

    runner.egraph.rebuild();
    let rules: Vec<Rewrite> = vec![rw!(
        "g-x";
        "(g x)" => "(f x)"
    )];
    runner = runner.with_iter_limit(2).run(&rules);

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[test]
fn chengs_example_slack_25_11_25() {
    // x := f(h(g(x)) := f(h(h(g(x))))
    // y := h(y)

    let rules: Vec<Rewrite> = vec![rw!(
        "g-f-z";
        "(g (f ?x))" => "?x"
    )];
    let runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(f (h (g x)))".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(h y)".parse().unwrap())
        .with_iter_limit(2)
        .run(&rules);

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
}

#[test]
fn chengs_example_slack_25_02_26() {
    // x = Cons(0, f(x))
    // y = Cons(0, g(y))
    // z = Cons(0, g(z))

    let mut runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(Cons 0 (f x))".parse().unwrap())
        .with_definition(&"z".parse().unwrap(), &"(Cons 0 (g z))".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(Cons 0 (g y))".parse().unwrap());

    // runner.egraph.rebuild();

    let gy = runner.egraph.add_expr(&"(g y)".parse().unwrap());
    let fy = runner.egraph.add_expr(&"(f y)".parse().unwrap());

    runner.egraph.rebuild();
    assert_eq!(
        runner.egraph.find(runner.roots[2]),
        runner.egraph.find(runner.roots[1])
    );
    runner.egraph.union(gy, fy);
    runner.egraph.rebuild();

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[2])
    );
}

#[test]
fn chengs_example_slack_26_02_26() {
    // x  := Cons(0, x1)
    // z  := Cons(0, z1)
    // x1 == x1 + x
    // z1 == z1 + z
    let mut egraph = EGraph::default();
    let x = egraph.add_definition(&"x".parse().unwrap(), &"(Cons 0 x1)".parse().unwrap());
    let z = egraph.add_definition(&"z".parse().unwrap(), &"(Cons 0 z1)".parse().unwrap());
    let x1 = egraph.add_expr(&"x1".parse().unwrap());
    let z1 = egraph.add_expr(&"z1".parse().unwrap());
    let x1_plus_x = egraph.add_expr(&"(+ x1 x)".parse().unwrap());
    let z1_plus_z = egraph.add_expr(&"(+ z1 z)".parse().unwrap());
    egraph.union(x1, x1_plus_x);
    egraph.union(z1, z1_plus_z);
    egraph.rebuild();
    assert_eq!(egraph.find(x.0), egraph.find(z.0));
}

//----------------------------------------------------------------------------//
// Rewriting over definitions
//----------------------------------------------------------------------------//
#[test]
fn rewrite_over_definitions() {
    // x := f(x)
    // y := f(f(x))
    let rules: Vec<Rewrite> = vec![rw!(
        "g-f-x";
        "(g (f ?x))" => "(f ?x)"
    )];
    let runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(f x)".parse().unwrap())
        .with_expr(&"(g x)".parse().unwrap())
        .with_iter_limit(2)
        .run(&rules);

    assert!(runner
        .egraph
        .check_bisimilar(runner.roots[0], runner.roots[1]));
}

#[test]
fn x_equal_tail_x() -> Result<(), std::io::Error> {
    // x := f(x)
    // y := f(f(x))
    let runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(Cons 0 x)".parse().unwrap())
        .with_expr(&"(Tail x)".parse().unwrap())
        .with_iter_limit(2)
        .run(&make_rules());

    runner.egraph.dot().to_dot("dots/tail_rewrite.dot")?;
    runner
        .egraph
        .dot()
        .automata_to_dot("dots/tail_rewrite_transition.dot")?;

    assert_eq!(
        runner.egraph.find(runner.roots[0]),
        runner.egraph.find(runner.roots[1])
    );
    Ok(())
}

#[test]
fn simple_lookthrough() -> Result<(), std::io::Error> {
    // x := y
    // x != y -> false
    let runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"y".parse().unwrap())
        .with_expr(&"(!= x y)".parse().unwrap())
        .with_expr(&"false".parse().unwrap())
        .with_iter_limit(2)
        .run(&make_rules());

    runner.egraph.dot().to_dot("dots/lookthrough.dot")?;

    assert_eq!(
        runner.egraph.find(runner.roots[1]),
        runner.egraph.find(runner.roots[2])
    );
    Ok(())
}

#[test]
fn cheng_example_slack_29_04_26() {
    // x := f (g x)
    // y := g (f y)
    // z := f y
    let runner = Runner::default()
        .with_definition(&"x".parse().unwrap(), &"(f (g x))".parse().unwrap())
        .with_definition(&"y".parse().unwrap(), &"(g (f y))".parse().unwrap())
        .with_definition(&"z".parse().unwrap(), &"(f y)".parse().unwrap());

    // runner.egraph.rebuild();
    // assert_eq!(runner.egraph.find(x.0), runner.egraph.find(z.0));
    assert!(runner
        .egraph
        .check_bisimilar(runner.roots[0], runner.roots[2]));
}

#[test]
fn cheng_example_slack_22_05_26() {
    // x := snd(x, 1)
    // y := snd(y, 2)

    // x and y should not be bisimilar

    let mut egraph = EGraph::default();
    let x = egraph.add_definition(&"x".parse().unwrap(), &"(Snd x 1)".parse().unwrap());
    let y = egraph.add_definition(&"y".parse().unwrap(), &"(Snd y 2)".parse().unwrap());

    let one = egraph.add_expr(&"1".parse().unwrap());
    let two = egraph.add_expr(&"2".parse().unwrap());

    egraph.union(x.1, one);
    egraph.union(y.1, two);

    assert!(!egraph.check_bisimilar(x.0, y.0));
}

// ----------------------------------------------------------------------------//
// PAPER Motivational Examples
// ----------------------------------------------------------------------------//
#[test]
fn paper_example_2() {
    // ones := cons(1, ones)
    // zero := cons(0, zero)
    // one' := map(incr, zero)
    let runner = Runner::default()
        .disable_definition_rebuilding()
        .with_explanations_enabled()
        .with_definition(&"ones".parse().unwrap(), &"(Cons 1 ones)".parse().unwrap())
        .with_definition(&"zero".parse().unwrap(), &"(Cons 0 zero)".parse().unwrap())
        .with_definition(
            &"one'".parse().unwrap(),
            &"(Map incr zero)".parse().unwrap(),
        )
        .run(&make_rules());

    runner
        .egraph
        .dot()
        .to_dot("dots/paper_example_2.dot")
        .unwrap();

    assert!(runner
        .egraph
        .check_bisimilar(runner.roots[0], runner.roots[2]));
}
