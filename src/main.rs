use clap::Parser;
use egg::{rewrite as rw, *};
use num_rational::BigRational;

define_language! {
    enum Math {
        Num(BigRational),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Symbol(Symbol),
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct MathAnalysis;
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
            Math::Mul([a, b]) => Some(c(a)? * c(b)?),
            _ => None,
        }
    }

    fn modify(egraph: &mut EGraph<Math, Self>, id: Id) {
        if let Some(n) = &egraph[id].data {
            let const_id = egraph.add(Math::Num(n.clone()));
            egraph.union(id, const_id);
        }
    }
}

fn rules() -> Vec<Rewrite<Math, MathAnalysis>> {
    vec![
        // add
        rw!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("add-assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("add-same"; "(+ ?a ?a)" => "(* ?a 2)"),
        // mul
        rw!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("mul-assoc"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
    ]
}

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
