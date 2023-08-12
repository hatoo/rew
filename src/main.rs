use clap::Parser;
use egg::{rewrite as rw, *};
use num::Zero;
use num_rational::BigRational;
use num_traits::pow::Pow;

define_language! {
    pub enum Math {
        Num(BigRational),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        // Short hand to unary minus
        "-" = Minus(Id),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "expt" = Expt([Id; 2]),
        Symbol(Symbol),
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct MathAnalysis;
impl Analysis<Math> for MathAnalysis {
    type Data = Option<BigRational>;
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        match (&a, &b) {
            (None, Some(_)) => {
                *a = b.clone();
                DidMerge(true, false)
            }
            (Some(_), None) => DidMerge(false, true),
            _ => DidMerge(false, false),
        }
    }

    fn make(egraph: &EGraph<Math, Self>, enode: &Math) -> Self::Data {
        let c = |i: &Id| egraph[*i].data.clone();
        match enode {
            Math::Num(n) => Some(n.clone()),
            Math::Add([a, b]) => Some(c(a)? + c(b)?),
            Math::Sub([a, b]) => Some(c(a)? - c(b)?),
            Math::Minus(a) => Some(-c(a)?),
            Math::Mul([a, b]) => Some(c(a)? * c(b)?),
            Math::Div([a, b]) => {
                let b = c(b)?;
                if b.is_zero() {
                    None
                } else {
                    Some(c(a)? / b)
                }
            }
            Math::Expt([a, b]) => {
                let b = c(b)?;
                if b.is_integer() {
                    Some(c(a)?.pow(b.to_integer()))
                } else {
                    None
                }
            }
            Math::Symbol(_) => None,
        }
    }

    fn modify(egraph: &mut EGraph<Math, Self>, id: Id) {
        if let Some(n) = &egraph[id].data {
            let const_id = egraph.add(Math::Num(n.clone()));
            egraph.union(id, const_id);
        }
    }
}

macro_rules! flat_vec {
    (flat $elem:expr $(,)?) => {
        $elem
    };
    ($elem:expr $(,)?) => {
        vec![$elem]
    };
    (
        flat $elem:expr ,
        $($rest:tt)+
    )  => {{
        let mut t = $elem;
        t.extend(flat_vec!($($rest)+));
        t
    }};
    (
        $elem:expr ,
        $($rest:tt)+
     ) => {{
        let mut t = vec![$elem];
        t.extend(flat_vec!($($rest)+));
        t
    }};
}

#[test]
fn test_flat_vec() {
    assert_eq!(flat_vec!(1), vec![1]);
    assert_eq!(flat_vec!(1, 2), vec![1, 2]);
    assert_eq!(flat_vec!(1, 2, 3), vec![1, 2, 3]);
    assert_eq!(flat_vec!(flat vec![1], 2), vec![1, 2]);
    assert_eq!(flat_vec!(1, flat vec![2]), vec![1, 2]);
}

pub fn rules() -> Vec<Rewrite<Math, MathAnalysis>> {
    flat_vec![
        // add
        rw!("[add] commutative law"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("[add] associative property"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("[add] identity"; "(+ ?a 0)" => "?a"),
        // mul
        rw!("[mul] commutative law"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("[mul] associative property"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        flat rw!("[mul] identity"; "(* ?a 1)" <=> "?a"),
        rw!("[mul] zero"; "(* ?a 0)" => "0"),
        rw!("[mul] distribution"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        // sub
        flat rw!("[sub] to mul"; "(- ?a ?b)" <=> "(+ ?a (* -1 ?b))"),
        rw!("[sub] cancel"; "(+ ?a (* -1 ?a))" => "0"),
        flat rw!("[sub] shorten"; "(- 0 ?a)" <=> "(- ?a)"),
        // rw!("[sub] cancel"; "(+ ?a (- ?b ?a))" => "?b"),
        // rw!("[sub] inv inv"; "(- 0 (- 0 ?a))" => "?a"),
        // mul and others
        /*
        // div
        rw!("div-1"; "(/ ?a 1)" => "?a"),
        rw!("div-0"; "(/ 0 ?a)" => "0" if is_not_zero("?a")),
        rw!("div-same"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),
        // expt
        rw!("expt-0"; "(expt ?a 0)" => "1"),
        rw!("expt-mul"; "(* (expt ?a ?b) (expt ?a ?c))" => "(expt ?a (+ ?b ?c))"),
        // Just for fun
        rw!("ii"; "(* i i)" => "-1"),
        // TODO categorize more better
        rw!("mul-add"; "(+ (* ?a ?x) (* ?b ?x))" => "(* (+ ?a ?b) ?x)"),
        rw!("mul-sub"; "(- (* ?a ?x) (* ?b ?x))" => "(* (- ?a ?b) ?x)"),
        // distributive
        rw!("mul-add-distributive"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("mul-sub-distributive"; "(* ?a (- ?b ?c))" => "(- (* ?a ?b) (* ?a ?c))"),
        */
    ]
    // lr.extend(rw!("mul-1"; "(* ?a 1)" <=> "?a"));
    // lr.extend(rw!("expt-1"; "(expt ?a 1)" <=> "?a"));
}

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph<Math, MathAnalysis>, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Math::Num(BigRational::zero());
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}

// add
// Currently, the following rules are directly written in the rules() but perhaps we can describe it in a less number of rules.
test_fn! {math_add_const, rules(), "(+ 1 2)" => "3"}
test_fn! {math_add_comm, rules(), "(+ x y)" => "(+ y x)"}
test_fn! {math_add_assoc_lr, rules(), "(+ (+ x y) z)" => "(+ x (+ y z))"}
test_fn! {math_add_assoc_rl, rules(), "(+ x (+ y z))" => "(+ (+ x y) z)"}
test_fn! {math_mul_assoc_lr, rules(), "(* (* x y) z)" => "(* x (* y z))"}
test_fn! {math_mul_assoc_rl, rules(), "(* x (* y z))" => "(* (* x y) z)"}
test_fn! {math_add_id, rules(), "(+ x 0)" => "x"}
test_fn! {math_add_inv, rules(), "(+ x (- y x))" => "y"}

test_fn! {math_sub_cancel, rules(), "(- (+ a b) a)" => "b"}
test_fn! {math_sub_cancel2, rules(), "(- (+ (+ a b) (+ c d)) a)" => "(+ b (+ c d))"}
test_fn! {math_sub_id, rules(), "(- a 0)" => "a"}
test_fn! {math_sub_sub, rules(), "(- 0 (- 0 a))" => "a"}
test_fn! {math_sub_sub2, rules(), "(- b (- 0 a))" => "(+ a b)"}
test_fn! {math_sub_from_mul, rules(), "(+ ?a (* -1 ?b))" => "(- ?a ?b)"}

// const prop
test_fn! {math_const_prop, rules(), "(+ 1 (+ 2 3))" => "6"}
test_fn! {math_partial_eval, rules(), "(* 4 (* 2 x))" => "(* 8 x)"}

/// Formula rewriter using egraph.
///
/// Supported operations: +, -, *, /, expt
#[derive(Debug, Parser)]
struct Opts {
    formula: RecExpr<Math>,
}

fn main() {
    let opts = Opts::parse();
    let rules = rules();
    let runner = Runner::default().with_expr(&opts.formula).run(&rules);

    let extractor = Extractor::new(&runner.egraph, AstSize);

    let (_best_cost, bext_expr) = extractor.find_best(runner.roots[0]);

    println!("{}", bext_expr.pretty(80));
}
