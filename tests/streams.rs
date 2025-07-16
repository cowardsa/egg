use egg::*;

define_language! {
    enum StreamLanguage {
        Num(i32),
        "Cons" = Cons([Id; 2]),
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
    egraph.rebuild_observations();
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
    runner.egraph.rebuild_observations();
    
    assert_eq!(runner.egraph.find(ids_ab.0), runner.egraph.find(ids_ba.0));


}
