use egg::rewrite as rw;
use egg::*;

type EGraph = egg::EGraph<ElementaryLanguage, ()>;
type Runner = egg::Runner<ElementaryLanguage, ()>;
type Rewrite = egg::Rewrite<ElementaryLanguage, ()>;

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
        rw!("neg-mul"; "(* (- ?a) ?b)" => "(- (* ?a ?b))"),
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

fn compute_derivative(expr: RecExpr<ElementaryLanguage>) -> RecExpr<ElementaryLanguage> {
    let mut runner: Runner = Runner::default().with_expr(&expr);
    runner = runner.run(&make_derivative_rules());
    let extractor = Extractor::new(&runner.egraph, SillyCostFn);
    extractor.find_best(runner.roots[0]).1
}

fn simplify(expr: RecExpr<ElementaryLanguage>) -> RecExpr<ElementaryLanguage> {
    let mut runner: Runner = Runner::default().with_expr(&expr);
    runner = runner.run(&make_simplification_rules());
    let extractor = Extractor::new(&runner.egraph, AstSize);
    extractor.find_best(runner.roots[0]).1
}

#[test]
fn cos_asin() {
    // Basic example of derivative
    let sqrt_one_minus_xsquared = "(D x (sqrt (- 1 (* x x))))".parse().unwrap();
    let sqrt_derivative = simplify(compute_derivative(sqrt_one_minus_xsquared));
    println!("D sqrt(1-x^2) {}", sqrt_derivative);
    let cos_asin = "(D x (cos (asin x)))".parse().unwrap();
    let cos_asin_derivative = simplify(compute_derivative(cos_asin));
    println!("D cos(asin(x)) {}", cos_asin_derivative);

    let mut runner = Runner::default();
    let lhs_id = runner.egraph.add_expr(&cos_asin_derivative);
    let rhs_id = runner.egraph.add_expr(&sqrt_derivative);
    runner = runner.run(&make_unification_rules());

    assert_eq!(runner.egraph.find(lhs_id), runner.egraph.find(rhs_id));
}

#[test]
fn sin_acos() {
    // Basic example of derivative
    let sqrt_one_minus_xsquared = "(D x (sqrt (- 1 (* x x))))".parse().unwrap();
    let sqrt_derivative = simplify(compute_derivative(sqrt_one_minus_xsquared));
    println!("D sqrt(1-x^2) {}", sqrt_derivative);
    let sin_acos = "(D x (sin(acos x))))".parse().unwrap();
    let sin_acos_derivative = simplify(compute_derivative(sin_acos));
    println!("D sin(acos(x)) {}", sin_acos_derivative);

    let mut runner = Runner::default();
    let lhs_id = runner.egraph.add_expr(&sin_acos_derivative);
    let rhs_id = runner.egraph.add_expr(&sqrt_derivative);
    runner = runner.run(&make_unification_rules());

    assert_eq!(runner.egraph.find(lhs_id), runner.egraph.find(rhs_id));
}
