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

// TODO: do we want to separate out some of these rules into unification rules?
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
        rw!("neg-neg"; "(- (- ?a))" => "?a"),
        rw!("add-neg"; "(+ ?a (- ?b))" => "(- ?a ?b)"),
        rw!("neg-add"; "(- ?a ?b)" => "(+ ?a (- ?b))"),
        rw!("neg-sub"; "(+ (- ?a) ?b)" => "(- (- ?a ?b))"),
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

fn equal_under_observation(
    lhs: &RecExpr,
    rhs: &RecExpr,
    lhs_obs: &RecExpr,
    rhs_obs: &RecExpr,
    assumption: &Vec<(&RecExpr, &RecExpr)>,
    debug: bool,
) -> bool {
    let mut runner: Runner = Runner::default();
    let lhs_ids = runner.egraph.add_observation(&lhs, lhs_obs);
    let rhs_ids = runner.egraph.add_observation(&rhs, rhs_obs);
    for (lhs_assume, rhs_assume) in assumption.iter() {
        let lhs_assume_id = runner.egraph.add_expr(lhs_assume);
        let rhs_assume_id = runner.egraph.add_expr(rhs_assume);
        runner.egraph.union(lhs_assume_id, rhs_assume_id);
        runner.egraph.rebuild();
    }
    runner = runner.run(&make_unification_rules());
    if debug {
        runner.print_report();
    }
    return runner.egraph.find(lhs_ids.0) == runner.egraph.find(rhs_ids.0);
}

fn equal_under_assumption(
    lhs: &RecExpr,
    rhs: &RecExpr,
    assumption: &Vec<(&RecExpr, &RecExpr)>,
    debug: bool,
) -> bool {
    let mut runner: Runner = Runner::default();
    let lhs_id = runner.egraph.add_expr(&lhs);
    let rhs_id = runner.egraph.add_expr(&rhs);
    for (lhs_assume, rhs_assume) in assumption.iter() {
        let lhs_assume_id = runner.egraph.add_expr(lhs_assume);
        let rhs_assume_id = runner.egraph.add_expr(rhs_assume);
        runner.egraph.union(lhs_assume_id, rhs_assume_id);
        runner.egraph.rebuild();
    }
    runner = runner.run(&make_unification_rules());
    if debug {
        runner.print_report();
    }
    return runner.egraph.find(lhs_id) == runner.egraph.find(rhs_id);
}
fn evaluate(expr: &RecExpr, var: String, h: i32) -> i32 {
    h
}

fn check_equality(
    lhs_in: &RecExpr,
    rhs_in: &RecExpr,
    unroll_limit: usize,
    with_assumptions: Vec<(&RecExpr, &RecExpr)>,
) -> bool {
    let lhs = simplify(lhs_in);
    let rhs = simplify(rhs_in);

    if equal_under_assumption(&lhs, &rhs, &with_assumptions, false) {
        return true;
    }
    let mut new_assumptions = with_assumptions.clone();
    new_assumptions.push((&lhs, &rhs));
    let mut d_lhs = lhs.clone();
    let mut d_rhs = rhs.clone();
    let mut eval_lhs = vec![];
    let mut eval_rhs = vec![];
    for step in 0..unroll_limit {
        // Evaluate at point h
        eval_lhs.push(evaluate(&d_lhs, "x".to_string(), 0));
        eval_rhs.push(evaluate(&d_rhs, "x".to_string(), 0));

        // TODO: incorporate the variable name into check_equality
        d_lhs = simplify(&compute_derivative("x".to_string(), &d_lhs));
        d_rhs = simplify(&compute_derivative("x".to_string(), &d_rhs));

        let mut observable_lhs = format!("{}", d_lhs);
        let mut observable_rhs = format!("{}", d_rhs);
        for i in (0..step + 1).rev() {
            observable_lhs = format!("(Cons {} {})", eval_lhs[i], observable_lhs);
            observable_rhs = format!("(Cons {} {})", eval_rhs[i], observable_rhs);
        }

        let lhs_obs = observable_lhs.parse().unwrap();
        let rhs_obs = observable_rhs.parse().unwrap();

        if equal_under_observation(&lhs, &rhs, &lhs_obs, &rhs_obs, &with_assumptions, false) {
            return true;
        } else if step + 1 >= unroll_limit {
            // last iteration and unable to prove
            let equal_by_assumption =
                equal_under_assumption(&d_lhs, &d_rhs, &new_assumptions, false);

            println!(
                "Not observationally equal after {} derivatives:\n{} != {}\nlhs->{}\nrhs->{}",
                unroll_limit, lhs, rhs, lhs_obs, rhs_obs
            );
            equal_under_observation(&lhs, &rhs, &lhs_obs, &rhs_obs, &with_assumptions, true);

            if equal_by_assumption {
                println!("However they are equal by assumption!");
            }
            return false;
        }
        // TODO: add a check for equality of application at h
    }
    return false;
}

#[test]
fn choose_observation() {
    // let mut egraph = EGraph::default();
    let mut runner = Runner::default();
    // let f = egraph.add_expr(&"f".parse().unwrap());
    // let g = egraph.add_expr(&"g".parse().unwrap());
    // let two_f = egraph.add_expr();
    // let two_g = egraph.add_expr(&"(* g g)".parse().unwrap());

    let f = runner
        .egraph
        .add_observation(&"f".parse().unwrap(), &"(Cons 1 (+ f f))".parse().unwrap());
    let g = runner
        .egraph
        .add_observation(&"g".parse().unwrap(), &"(Cons 1 (* g 2))".parse().unwrap());
    runner = runner.run(&make_simplification_rules());
    runner.egraph.dot().to_dot("choose_obs.dot");

    assert_eq!(runner.egraph.find(f.0), runner.egraph.find(g.0))
}

#[test]
fn simple_observation() {
    // let mut egraph = EGraph::default();
    let mut runner = Runner::default();
    // let f = egraph.add_expr(&"f".parse().unwrap());
    // let g = egraph.add_expr(&"g".parse().unwrap());
    // let two_f = egraph.add_expr();
    // let two_g = egraph.add_expr(&"(* g g)".parse().unwrap());

    let f = runner.egraph.add_observation(
        &"f".parse().unwrap(),
        &"(Cons 1 (* 2 (- f)))".parse().unwrap(),
    );
    let g = runner.egraph.add_observation(
        &"g".parse().unwrap(),
        &"(Cons 1 (- (* 2 g)))".parse().unwrap(),
    );
    runner = runner.run(&make_unification_rules());
    runner.egraph.rebuild_observations();
    runner.egraph.dot().to_dot("simple_obs.dot");

    assert_eq!(runner.egraph.find(f.0), runner.egraph.find(g.0))
}
#[test]
fn cos_asin() {
    // Basic example of derivative
    let sqrt_one_minus_xsquared = "(sqrt (- 1 (* x x)))".parse().unwrap();
    let cos_asin = "(cos (asin x))".parse().unwrap();

    assert!(check_equality(
        &sqrt_one_minus_xsquared,
        &cos_asin,
        1,
        vec![]
    ));
}

#[test]
fn sin_acos() {
    // Basic example of derivative
    let sqrt_one_minus_xsquared = "(sqrt (- 1 (* x x)))".parse().unwrap();
    let sin_acos = "(sin(acos x)))".parse().unwrap();

    assert!(check_equality(
        &sqrt_one_minus_xsquared,
        &sin_acos,
        1,
        vec![]
    ));
}

#[test]
fn sin2x() {
    // Basic example of derivative
    let sin_2x = "(sin (* 2 x))".parse().unwrap();
    let sin_cos = "(* 2 (* (sin x) (cos x)))".parse().unwrap();

    assert!(check_equality(&sin_2x, &sin_cos, 2, vec![]));
}

#[test]
fn cos2x() {
    // Basic example of derivative
    let cos_2x = "(cos (* 2 x))".parse().unwrap();
    let sin_cos = "(- (* (cos x) (cos x)) (* (sin x) (sin x))))"
        .parse()
        .unwrap();

    assert!(check_equality(&cos_2x, &sin_cos, 2, vec![]));

    let cossq = "(- (* 2 (* (cos x) (cos x))) 1))".parse().unwrap();
    assert!(check_equality(
        &cos_2x,
        &cossq,
        2,
        vec![(&cos_2x, &sin_cos)]
    ));

    let sinsq = "(- 1 (* 2 (* (sin x) (sin x))))".parse().unwrap();
    assert!(check_equality(
        &cos_2x,
        &sinsq,
        2,
        vec![(&cos_2x, &sin_cos)]
    ));
}

#[test]
fn sinsq_plus_cossq() {
    // Basic example of derivative
    let sinx = "(* (sin x) (sin x))".parse().unwrap();
    let cosx = "(- 1 (* (cos x) (cos x)))".parse().unwrap();

    assert!(check_equality(&sinx, &cosx, 1, vec![]));
}

#[test]
fn sin_half_angle() {
    // Basic example of derivative
    let sinx = "(* (sin (/ x 2)) (sin (/ x 2)))".parse().unwrap();
    let cosx = "(/ (- 1 (cos x)) 2))".parse().unwrap();

    assert!(check_equality(&sinx, &cosx, 1, vec![]));
}
