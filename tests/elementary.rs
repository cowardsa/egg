use egg::rewrite as rw;
use egg::*;

type EGraph = egg::EGraph<ElementaryLanguage, ()>;
type Runner = egg::Runner<ElementaryLanguage, ()>;
type Rewrite = egg::Rewrite<ElementaryLanguage, ()>;
type RecExpr = egg::RecExpr<ElementaryLanguage>;

define_language! {
    enum ElementaryLanguage {
        Num(i32),
        "Cons" = Cons([Id; 2]),

        // Algebraic
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "-" = Negate([Id; 1]),
        "sqrt" = SquareRoot([Id; 1]),

        // Derivative
        "D" = Derivative([Id; 2]),

        // Elementary functions
        "exp" = Exponential([Id; 1]),
        "cos" = Cosine([Id; 1]),
        "sin" = Sine([Id; 1]),
        "acos" = Arccos([Id; 1]),
        "asin" = Arcsine([Id; 1]),


        Symbol(Symbol),
    }
}

struct SillyCostFn;
impl CostFunction<ElementaryLanguage> for SillyCostFn {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &ElementaryLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            ElementaryLanguage::Derivative(_) => 100.0,
            _ => 1.0,
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

fn make_unification_rules() -> Vec<Rewrite> {
    let mut rules = make_simplification_rules();
    rules.extend(vec![
        // Unification rules
        rw!("div-mul"; "(/ ?a (* ?b ?c))" => "(* (/ ?a ?b) (/ ?a ?c))"),
        rw!("mul-div"; "(* ?a (/ ?b ?c))" => "(/ (* ?a ?b) ?c)"),
        rw!("mul-div-same"; "(/ (* ?a ?b) ?a))" => "?b"),
        rw!("neg-div"; "(/ (- ?a) ?b)" => "(- (/ ?a ?b))"),
        rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
    ]);
    rules
}

fn make_simplification_rules() -> Vec<Rewrite> {
    vec![
        // Simplification rules
        rw!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("mul-one"; "(* ?a 1)" => "?a"),
        rw!("mul-zero"; "(* ?a 0)" => "0"),
        rw!("add-zero"; "(+ ?a 0)" => "?a"),
        rw!("add-same"; "(+ ?a ?a)" => "(* 2 ?a)"),
        rw!("sub-zero"; "(- ?a 0)" => "?a"),
        rw!("zero-sub"; "(- 0 ?a)" => "(- ?a)"),
        rw!("neg-mul"; "(* (- ?a) ?b)" => "(- (* ?a ?b))"),
        // Elementary Inverses
        rw!("sin-asin"; "(sin (asin ?a))" => "?a"),
        rw!("cos-acos"; "(cos (acos ?a))" => "?a"),
        rw!("asin-sin"; "(asin (sin ?a))" => "?a"),
        rw!("acos-cos"; "(acos (cos ?a))" => "?a"),
    ]
}

fn make_derivative_rules() -> Vec<Rewrite> {
    let mut rules = vec![
        rw!("exp-derive"; "(D ?a (exp ?a))" => "(exp ?a)"),
        rw!("cos-derive"; "(D ?a (cos ?a))" => "(- (sin ?a))"),
        rw!("sin-derive"; "(D ?a (sin ?a))" => "(cos ?a)"),
        rw!("acos-derive"; "(D ?a (acos ?a))" => "(/ (- 1) (sqrt (- 1 (* ?a ?a))))"),
        rw!("asin-derive"; "(D ?a (asin ?a))" => "(/ 1 (sqrt (- 1 (* ?a ?a))))"),
        rw!("sqrt-derive"; "(D ?a (sqrt ?a))" => "(/ 1 (* 2 (sqrt ?a)))"),
        // Basic Derivative Rules
        rw!("const-derive-1"; "(D ?a 1)" => "0"),
        rw!("const-derive-2"; "(D ?a 2)" => "0"),
        rw!("var-derive"; "(D ?a ?a)" => "1"),
        rw!("mul-derive"; "(D ?a (* ?b ?c))" => "(+ (* (D ?a ?b) ?c) (* ?b (D ?a ?c)))"),
        rw!("add-derive"; "(D ?a (+ ?b ?c))" => "(+ (D ?a ?b) (D ?a ?c))"),
        rw!("sub-derive"; "(D ?a (- ?b ?c))" => "(- (D ?a ?b) (D ?a ?c))"),
        rw!("neg-derive"; "(D ?a (- ?b))" => "(- (D ?a ?b))"),
    ];

    let elem_funcs = vec!["exp", "cos", "sin", "sqrt", "acos", "asin"];
    for elem in elem_funcs.iter() {
        let func = elem.to_string();
        let rule = format!("{}-chain", func);
        let lhs: Pattern<ElementaryLanguage> = format!("(D ?a ({} ?b))", func).parse().unwrap();
        let rhs: Pattern<ElementaryLanguage> = format!("(* (D ?b ({} ?b)) (D ?a ?b))", func)
            .parse()
            .unwrap();
        rules.push(rw!(rule; lhs => rhs));
    }
    rules
}

fn compute_derivative(var: String, expr: &RecExpr) -> RecExpr {
    let d_expr = format!("(D {} {})", var, expr).parse().unwrap();
    let mut runner: Runner = Runner::default().with_expr(&d_expr);
    runner = runner.run(&make_derivative_rules());
    let extractor = Extractor::new(&runner.egraph, SillyCostFn);
    extractor.find_best(runner.roots[0]).1
}

fn simplify(expr: &RecExpr) -> RecExpr {
    let mut runner: Runner = Runner::default().with_expr(expr);
    runner = runner.run(&make_simplification_rules());
    let extractor = Extractor::new(&runner.egraph, AstSize);
    extractor.find_best(runner.roots[0]).1
}

fn equal_under_assumption(
    lhs: &RecExpr,
    rhs: &RecExpr,
    assumption: Option<(&RecExpr, &RecExpr)>,
) -> bool {
    let mut runner: Runner = Runner::default();
    let lhs_id = runner.egraph.add_expr(&lhs);
    let rhs_id = runner.egraph.add_expr(&rhs);
    if let Some((lhs_assume, rhs_assume)) = assumption {
        let lhs_assume_id = runner.egraph.add_expr(&lhs_assume);
        let rhs_assume_id = runner.egraph.add_expr(&rhs_assume);
        runner.egraph.union(lhs_assume_id, rhs_assume_id);
    }
    runner = runner.run(&make_unification_rules());
    return runner.egraph.find(lhs_id) == runner.egraph.find(rhs_id);
}

fn check_equality(lhs_in: &RecExpr, rhs_in: &RecExpr, unroll_limit: usize) -> bool {
    let lhs = simplify(lhs_in);
    let rhs = simplify(rhs_in);

    if equal_under_assumption(&lhs, &rhs, None) {
        return true;
    }
    let mut d_lhs = lhs.clone();
    let mut d_rhs = rhs.clone();
    for i in 0..unroll_limit {
        // TODO: incorporate the variable name into check_equality
        d_lhs = simplify(&compute_derivative("x".to_string(), &d_lhs));
        d_rhs = simplify(&compute_derivative("x".to_string(), &d_rhs));

        // TODO: add a check for equality of application at zero
        if equal_under_assumption(&d_lhs, &d_rhs, Some((&lhs, &rhs))) {
            println!("Equal after {} derivatives", i + 1);
            return true;
        }
    }
    return false;
}

#[test]
fn cos_asin() {
    // Basic example of derivative
    let sqrt_one_minus_xsquared = "(sqrt (- 1 (* x x)))".parse().unwrap();
    let sqrt_derivative = simplify(&compute_derivative(
        "x".to_string(),
        &sqrt_one_minus_xsquared,
    ));
    println!("D sqrt(1-x^2) {}", sqrt_derivative);
    let cos_asin = "(cos (asin x))".parse().unwrap();
    let cos_asin_derivative = simplify(&compute_derivative("x".to_string(), &cos_asin));
    println!("D cos(asin(x)) {}", cos_asin_derivative);

    assert!(check_equality(&sqrt_one_minus_xsquared, &cos_asin, 1));
}

#[test]
fn sin_acos() {
    // Basic example of derivative
    let sqrt_one_minus_xsquared = "(sqrt (- 1 (* x x)))".parse().unwrap();
    let sqrt_derivative = simplify(&compute_derivative(
        "x".to_string(),
        &sqrt_one_minus_xsquared,
    ));
    println!("D sqrt(1-x^2) {}", sqrt_derivative);
    let sin_acos = "(sin(acos x)))".parse().unwrap();
    let sin_acos_derivative = simplify(&compute_derivative("x".to_string(), &sin_acos));
    println!("D sin(acos(x)) {}", sin_acos_derivative);

    let mut runner = Runner::default();
    let lhs_id = runner.egraph.add_expr(&sin_acos_derivative);
    let rhs_id = runner.egraph.add_expr(&sqrt_derivative);
    runner = runner.run(&make_unification_rules());

    assert_eq!(runner.egraph.find(lhs_id), runner.egraph.find(rhs_id));
}

#[test]
fn sin2x() {
    // Basic example of derivative
    let sin_2x = "(sin (* 2 x))".parse().unwrap();
    let d_sin_2x = simplify(&compute_derivative("x".to_string(), &sin_2x));
    let d_d_sin_2x = simplify(&compute_derivative("x".to_string(), &d_sin_2x));
    println!("D sin(2x) {}", d_sin_2x);
    println!("D D sin(2x) {}", d_d_sin_2x);

    let sin_cos = "(* 2 (* (sin x) (cos x)))".parse().unwrap();
    let d_sin_cos = simplify(&compute_derivative("x".to_string(), &sin_cos));
    let d_d_sin_cos = simplify(&compute_derivative("x".to_string(), &d_sin_cos));
    println!("D 2sin(x)cos(x)) {}", d_sin_cos);
    println!("D D 2sin(x)cos(x)) {}", d_d_sin_cos);

    assert!(equal_under_assumption(
        &d_d_sin_2x,
        &d_d_sin_cos,
        Some((&sin_2x, &sin_cos))
    ));
    // If we observe this shortcut then the lhs and rhs will be unified but they are not recognised
    // without this shortcut as we observe different node choices in the rebuilding step
    let shortcut = "(* 2 (* 2 (- (* 2 (* (sin x) (cos x))))))";
    let lhs_taylor = format!("(Cons 0 (Cons 2 {}))", d_d_sin_2x).parse().unwrap();
    let rhs_taylor = format!("(Cons 0 (Cons 2 {}))", d_d_sin_cos)
        .parse()
        .unwrap();

    // Add observations to the egraph
    let mut runner = Runner::default();
    let lhs: (Id, Id) = runner.egraph.add_observation(&sin_2x, &lhs_taylor);
    let rhs = runner.egraph.add_observation(&sin_cos, &rhs_taylor);
    runner = runner.run(&make_unification_rules());

    // assert_eq!(runner.egraph.find(lhs.0), runner.egraph.find(rhs.0));
}
