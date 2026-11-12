//! Knuth 7.7 / Baril et al. 2025: the trace DP over a decomposition is one pair.
//! Shape `RoseF<Op>` (the construction tree), plan `Project` (read the tree), algebra `TraceDp`
//! (the paper's per-node step). The output is a join/union expression; evaluating it in a
//! semiring is `formalism::expr::eval`, which is fusion along the measure homomorphism.
use crate::shape::RoseF;
use crate::{hylo, Algebra, Plan};
use alloc::vec::Vec;
use formalism::expr::{union, Expr};
use formalism::scheme::{step_node, Node, Table, Traced};

/// The plan that just reads an existing tree. Recursive because the tree is finite.
pub struct Project;
impl<Op> Plan<RoseF<Op>> for Project {
    type Seed = Node<Op>;
    fn unfold(&mut self, n: Node<Op>) -> (Op, Vec<Node<Op>>) { (n.op, n.children) }
}

pub struct TraceDp<'p, P>(pub &'p P);
impl<'p, P: Traced> Algebra<RoseF<P::Op>> for TraceDp<'p, P> {
    type Out = Table<P::Tau>;
    fn fold(&mut self, (op, kids): (P::Op, Vec<Table<P::Tau>>)) -> Table<P::Tau> { step_node(self.0, &op, kids) }
}

/// `⊎` of the accepted root rows: the expression of the solution set.
pub fn trace_dp<P: Traced>(p: &P, root: Node<P::Op>) -> Expr {
    let table = hylo::<RoseF<P::Op>, _, _>(&mut Project, &mut TraceDp(p), root);
    table.into_iter().filter(|r| p.accept(&r.tau)).fold(Expr::Empty, |e, r| union(e, r.expr))
}
