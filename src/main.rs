use clap::Parser;
use egg::{rewrite as rw, *};
use flat_vec::flat_vec;
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
        // Short hand to expt 2
        "sqrt" = Sqrt(Id),
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
                let a = c(a)?;
                let b = c(b)?;
                if !(a.is_zero() && b < BigRational::zero()) && b.is_integer() {
                    Some(a.pow(b.to_integer()))
                } else {
                    None
                }
            }
            Math::Sqrt(_) => None,
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
        flat rw!("[mul] distribution"; "(* ?a (+ ?b ?c))" <=> "(+ (* ?a ?b) (* ?a ?c))"),
        // sub
        flat rw!("[sub] to mul"; "(- ?a ?b)" <=> "(+ ?a (* -1 ?b))"),
        flat rw!("[sub] shorten"; "(- 0 ?a)" <=> "(- ?a)"),
        // div
        flat rw!("[div] to expt"; "(/ ?a ?b)" <=> "(* ?a (expt ?b -1))"),
        // expt
        flat rw!("[expt] identity"; "(expt ?a 1)" <=> "?a"),
        rw!("[expt] zero"; "(expt ?a 0)" => "1"),
        rw!("[expt] mul"; "(* (expt ?a ?b) (expt ?a ?c))" => "(expt ?a (+ ?b ?c))"),
        // sqrt
        flat rw!("[sqrt] to expt"; "(sqrt ?a)" <=> "(expt ?a 1/2)"),

        // complex
        flat rw!("i define"; "(expt -1 1/2)" <=> "i"),
    ]
}

/*
fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph<Math, MathAnalysis>, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Math::Num(BigRational::zero());
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}
*/

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

test_fn! {math_div_cancel, rules(), "(/ x x)" => "1"}
test_fn! {math_div_2, rules(), "(/ (* x x) x)" => "x"}

test_fn! {math_expt_mul, rules(), "(* (* x x) (* x x))" => "(expt x 4)"}

test_fn! {math_complex_i, rules(), "(* i i)" => "-1"}

// const prop
test_fn! {math_const_prop, rules(), "(+ 1 (+ 2 3))" => "6"}
test_fn! {math_partial_eval, rules(), "(* 4 (* 2 x))" => "(* 8 x)"}

/// Formula rewriter using egraph.
///
/// Supported operations: +, -, *, /, expt
#[derive(Debug, Parser)]
struct Opts {
    formula: RecExpr<Math>,
    #[clap(short, long)]
    verbose: bool,
}

fn main() {
    let opts = Opts::parse();
    let rules = rules();
    let runner = if opts.verbose {
        Runner::default().with_explanations_enabled()
    } else {
        Runner::default()
    };

    let mut runner = runner.with_expr(&opts.formula).run(&rules);

    let extractor = Extractor::new(&runner.egraph, AstSize);

    let (_best_cost, bext_expr) = extractor.find_best(runner.roots[0]);

    if opts.verbose {
        eprintln!(
            "{}",
            runner
                .explain_equivalence(&opts.formula, &bext_expr)
                .get_flat_string()
        );
    }

    println!("{}", bext_expr.pretty(80));
}
