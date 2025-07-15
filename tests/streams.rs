use egg::*;

define_language! {
    enum StreamLanguage {
        Num(i32),
        "Cons" = Cons([Id; 2]),
        Symbol(Symbol),
    }
}



/// parse an expression, simplify it using egg, and pretty print it back out
// fn simplify(s: &str) -> String {
//     // parse the expression, the type annotation tells it which Language to use
//     let expr: RecExpr<StreamLanguage> = s.parse().unwrap();

//     // simplify the expression using a Runner, which creates an e-graph with
//     // the given expression and runs the given rules over it
//     let runner = Runner::default().with_expr(&expr).run(&make_rules());

//     // the Runner knows which e-class the expression given with `with_expr` is in
//     let root = runner.roots[0];

//     // use an Extractor to pick the best element of the root eclass
//     let extractor = Extractor::new(&runner.egraph, AstSize);
//     let (best_cost, best) = extractor.find_best(root);
//     println!("Simplified {} to {} with cost {}", expr, best, best_cost);
//     best.to_string()
// }

#[test]
fn simple_tests() {
    let mut egraph = EGraph::<StreamLanguage, ()>::default();
    let a = "a".parse().unwrap();
    let astream = "(Cons 1 a)".parse().unwrap();
    let ids = egraph.add_observation(&a, &astream);
    let b = "b".parse().unwrap();
    let bstream1 = "(Cons 1 b)".parse().unwrap();
    let bstream = "(Cons 1 (Cons 1 b))".parse().unwrap();
    let ids = egraph.add_observation(&b, &bstream);
    let ids = egraph.add_observation(&bstream, &bstream1);
    egraph.rebuild_observations()
}
