use egg::*;

define_language! {
    enum StreamLanguage {
        Num(i32),
        "Cons" = Cons([Id; 2]),
        "Node" = Node([Id; 3]),
        "+" = Add([Id; 2]),
        Symbol(Symbol),
    }
}

fn make_rules() -> Vec<Rewrite<StreamLanguage, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
    ]
}

#[test]
fn simple_tests() {
    let mut egraph = EGraph::<StreamLanguage, ()>::default();
    let a = "a".parse().unwrap();
    let astream = "(Cons 1 a)".parse().unwrap();
    let ids_a = egraph.add_observation(&a, &astream);
    let b = "b".parse().unwrap();
    // let bstream1 = "(Cons 1 b)".parse().unwrap();
    let bstream = "(Cons 1 (Cons 1 b))".parse().unwrap();
    let ids_b = egraph.add_observation(&b, &bstream);
    // egraph.add_observation(&bstream, &bstream);
    // egraph.add_observation(&bstream1, &bstream1);
    egraph.rebuild();
    assert_eq!(egraph.find(ids_a.0), egraph.find(ids_b.0));
}


#[test]
fn commutative() {
    let mut runner : egg::Runner<StreamLanguage, ()> = Runner::default();
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
    let mut egraph = EGraph::<StreamLanguage, ()>::default();
    
    let ids_a = egraph.add_observation(&"tree1".parse().unwrap(), &"(Node 1 tree1 tree1)".parse().unwrap());
    let ids_b = egraph.add_observation(&"tree2".parse().unwrap(), &"(Node 1 (Node 1 tree2 tree2) (Node 1 tree2 tree2))".parse().unwrap());
    egraph.rebuild();
    
    assert_eq!(egraph.find(ids_a.0), egraph.find(ids_b.0));
}

#[test]
fn simple_dfa() {
    let mut egraph = EGraph::<StreamLanguage, ()>::default();
    
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