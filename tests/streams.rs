use egg::*;
use egg::{rewrite as rw};
use std::collections::HashSet;

pub type EGraph = egg::EGraph<StreamLanguage, ConstantFold>;
pub type Rewrite = egg::Rewrite<StreamLanguage, ConstantFold>;

define_language! {
    enum StreamLanguage {
        Num(i32),
        "Cons" = Cons([Id; 2]),
        "Node" = Node([Id; 3]),
        "+" = Add([Id; 2]),
        "Map" = Map([Id; 2]),
        "App" = App([Id; 2]),
        Symbol(Symbol),
    }
}

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<StreamLanguage> for ConstantFold {
    type Data = (Option<(i32, PatternAst<StreamLanguage>)>, HashSet<i32>);

    fn make(egraph: &mut EGraph, enode: &StreamLanguage) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.0.as_ref().map(|d| d.0);
        let constant = match enode {
            StreamLanguage::Num(c) => Some((*c, format!("{}", c).parse().unwrap())),
            StreamLanguage::Add([a, b]) => {
                if x(a).is_some() && x(b).is_some() {
                    Some((x(a).unwrap() + x(b).unwrap(), format!("(+ {} {})", x(a).unwrap(), x(b).unwrap()).parse().unwrap()))
                } else {
                    None
                }
            },
            _ => None,
        };

        let y = |i: &Id| &egraph[*i].data.1;
        let mut set = HashSet::new();
        match enode {
            StreamLanguage::Num(c) => {set.insert(*c);},
            StreamLanguage::Cons([a, b]) => {set.union(&y(a));},
            _ => (),
        };
        (constant, set)
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(&mut to.0, from.0, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data.0 {
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

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn make_rules() -> Vec<Rewrite> {
    vec![
        rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("propagate-map"; "(Map ?func (Cons ?a ?b))" => "(Cons (App ?func ?a) (Map ?func ?b))"),
        rw!("apply-incr"; "(App incr ?a)" => "(+ ?a 1)")
    ]
}

#[test]
fn simple_tests() {
    let mut egraph = EGraph::default();
    let a = "a".parse().unwrap();
    let astream = "(Cons 1 a)".parse().unwrap();
    let ids_a = egraph.add_observation(&a, &astream);
    let b = "b".parse().unwrap();
    let bstream = "(Cons 1 (Cons 1 b))".parse().unwrap();
    let ids_b = egraph.add_observation(&b, &bstream);
    egraph.rebuild();
    assert_eq!(egraph.find(ids_a.0), egraph.find(ids_b.0));
}


#[test]
fn commutative() {
    let mut runner : egg::Runner<StreamLanguage, ConstantFold> = Runner::default();
    // let mut egraph = EGraph::<StreamLanguage, ()>::default();
    // let-rec ab = cons( (a + b) ab)
    let ab = "ab".parse().unwrap();
    let abstream = "(Cons (+ a b) ab)".parse().unwrap();
    let ids_ab = runner.egraph.add_observation(&ab, &abstream);
    // let-rec ba = cons( (b + a) ba)
    let ba = "ba".parse().unwrap();
    let bastream = "(Cons (+ b a) ba)".parse().unwrap();
    let ids_ba = runner.egraph.add_observation(&ba, &bastream);
    
    println!("E-Graph Size {}", runner.egraph.number_of_classes());
    runner = runner.run(&make_rules());
    println!("E-Graph Size {}", runner.egraph.number_of_classes());
    // runner.egraph.rebuild_observations();
    // runner.egraph.dot().to_dot("commute.dot");
    
    assert_eq!(runner.egraph.find(ids_ab.0), runner.egraph.find(ids_ba.0));
}

#[test]
fn simple_trees() {
    let mut egraph = EGraph::default();
    
    let ids_a = egraph.add_observation(&"tree1".parse().unwrap(), &"(Node 1 tree1 tree1)".parse().unwrap());
    let ids_b = egraph.add_observation(&"tree2".parse().unwrap(), &"(Node 1 (Node 1 tree2 tree2) (Node 1 tree2 tree2))".parse().unwrap());
    egraph.rebuild();
    
    assert_eq!(egraph.find(ids_a.0), egraph.find(ids_b.0));
}

#[test]
fn simple_dfa() {
    let mut egraph = EGraph::default();
    
    egraph.add_observation(&"one".parse().unwrap(), &"(Node False two three)".parse().unwrap());
    let two = egraph.add_observation(&"two".parse().unwrap(), &"(Node False four three)".parse().unwrap());
    let three = egraph.add_observation(&"three".parse().unwrap(), &"(Node False five three)".parse().unwrap());
    let four = egraph.add_observation(&"four".parse().unwrap(), &"(Node True five four)".parse().unwrap());
    let five = egraph.add_observation(&"five".parse().unwrap(), &"(Node True four four)".parse().unwrap());
    
    egraph.rebuild();
    egraph.dot().to_dot("dfa.dot");
    
    assert_eq!(egraph.find(two.0), egraph.find(three.0));
    assert_eq!(egraph.find(four.0), egraph.find(five.0));
}

#[test]
fn map() {
    let mut runner : egg::Runner<StreamLanguage, ConstantFold> = Runner::default();
    let alt = runner.egraph.add_observation(&"alt".parse().unwrap(), &"(Cons 1 (Cons 2 alt))".parse().unwrap());
    let map = runner.egraph.add_expr(&"(Map incr alt)".parse().unwrap());
    runner = runner.run(&make_rules());
    runner.egraph.dot().to_dot("map.dot");

    // Check (map alt) = 2 :: 3 :: (map alt)
    assert_eq!(
        runner.egraph.add_expr(&"(Cons 2 (Cons 3 (Map incr alt)))".parse().unwrap()),
        runner.egraph.find(map)
    );
}