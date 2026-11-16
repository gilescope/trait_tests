//! Knuth 7.7 / Baril et al. 2025: the trace DP over a decomposition is one pair.
//! Shape `RoseF<Op>` (the construction tree), plan `Project` (read the tree), algebra `TraceDp`
//! (the paper's per-node step). The output is a join/union expression; evaluating it in a
//! semiring is `formalism::expr::eval`, which is fusion along the measure homomorphism.
use crate::shape::{hylo_rose, RoseAlgebra, RosePlan};
use alloc::vec::Vec;
use formalism::expr::{union, Expr};
use formalism::scheme::{step_node, Node, Table, Traced};

/// The plan that just reads an existing tree. Recursive because the tree is finite.
pub struct Project;
impl<Op> RosePlan<Op> for Project {
    type Seed = Node<Op>;
    fn unfold(&mut self, n: Node<Op>) -> (Op, Vec<Node<Op>>) { (n.op, n.children) }
}

pub struct TraceDp<'p, P>(pub &'p P);
impl<'p, P: Traced> RoseAlgebra<P::Op> for TraceDp<'p, P> {
    type Out = Table<P::Tau>;
    fn fold(&mut self, (op, kids): (P::Op, Vec<Table<P::Tau>>)) -> Table<P::Tau> { step_node(self.0, &op, kids) }
}

/// `⊎` of the accepted root rows: the expression of the solution set.
pub fn trace_dp<P: Traced>(p: &P, root: Node<P::Op>) -> Expr {
    let mut table = hylo_rose(&mut Project, &mut TraceDp(p), root);
    table.reverse();
    let mut e = Expr::Empty;
    while let Some(row) = table.pop() { if p.accept(&row.tau) { e = union(e, row.expr); } }
    e
}

/// `scheme::solve` as a root of this crate: the extraction (`earth +extract`) starts from named
/// items of `hylo`, and Charon drops a start item that lives in a dependency.
pub fn solve_scheme<P: Traced>(p: &P, root: &Node<P::Op>) -> Expr { formalism::scheme::solve(p, root) }

/// The `Bits` instance as a root: its `Traced` impl is extracted with `solve` instantiated.
pub fn solve_bits(p: &formalism::instances::bits::Bits, root: &Node<formalism::instances::bits::Op>) -> Expr {
    formalism::scheme::solve(p, root)
}
