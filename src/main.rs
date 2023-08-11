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

pub fn rules() -> Vec<Rewrite<Math, MathAnalysis>> {
    let mut lr = vec![
        // add
        rw!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("add-same"; "(+ ?a ?a)" => "(* ?a 2)"),
        // sub
        rw!("sub-0"; "(- ?a 0)" => "?a"),
        rw!("sub-same"; "(- ?a ?a)" => "0"),
        // mul
        rw!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("mul-assoc"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        // div
        rw!("div-1"; "(/ ?a 1)" => "?a"),
        rw!("div-0"; "(/ 0 ?a)" => "0" if is_not_zero("?a")),
        rw!("div-same"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),
        // expt
        rw!("expt-0"; "(expt ?a 0)" => "1"),
        rw!("expt-1"; "(expt ?a 1)" => "?a"),
        rw!("expt-2"; "(* ?a ?a)" => "(expt ?a 2)"),
        rw!("expt-mul"; "(* (expt ?a ?b) (expt ?a ?c))" => "(expt ?a (+ ?b ?c))"),
        // Just for fun
        rw!("ii"; "(* i i)" => "-1"),
        // TODO categorize more better
        rw!("mul-add"; "(+ (* ?a ?x) (* ?b ?x))" => "(* (+ ?a ?b) ?x)"),
        rw!("mul-sub"; "(- (* ?a ?x) (* ?b ?x))" => "(* (- ?a ?b) ?x)"),
    ];
    lr.extend(rw!("mul-1"; "(* ?a 1)" <=> "?a"));
    lr
}

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph<Math, MathAnalysis>, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Math::Num(BigRational::zero());
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}

test_fn! {math_const_prop, rules(), "(+ 1 (+ 2 3))" => "6"}
test_fn! {math_partial_eval, rules(), "(* 4 (* 2 x))" => "(* 8 x)"}

/// Formula rewriter using egraph.
///
/// Supported operations: +, -, *, /
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
