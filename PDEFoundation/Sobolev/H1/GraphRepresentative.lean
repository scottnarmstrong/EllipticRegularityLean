module

public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph

/-!
# Representatives of the complete Sobolev graph

Recover an actual weakly differentiable representative from the quotient graph.
The value and gradient are the canonical representatives of its two `L²`
components, and the weak identity follows from graph membership.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

namespace H1Graph

/-- Recover native value and gradient representatives of a complete `H¹` point. -/
def toH1Function {d : ℕ} {U : Set (Vec d)} (z : H1Graph U) : H1Function U where
  toFun := z.1.1
  grad := fun x => (z.1.2 x).toVec
  memL2 := Lp.memLp z.1.1
  gradMemL2 := by
    apply gradMemLpOn_iff_memLp_toHilbertVecField.mpr
    have h : toHilbertVecField (fun x => (z.1.2 x).toVec) = ⇑z.1.2 := by
      funext x
      simp only [toHilbertVecField, Vec.toHilbertVec_toVec]
    rw [h]
    exact Lp.memLp z.1.2
  hasWeakGradient := by
    intro i
    rw [hasWeakPartialDerivOn_iff_forall_testFunction]
    intro φ
    exact eq_neg_iff_add_eq_zero.mpr
      ((mem_weakGradientGraph_iff_integral z.1).mp z.2 i φ)

@[simp]
theorem toH1Function_toFun {d : ℕ} {U : Set (Vec d)} (z : H1Graph U) :
    z.toH1Function.toFun = ⇑z.1.1 := rfl

@[simp]
theorem toH1Function_grad {d : ℕ} {U : Set (Vec d)} (z : H1Graph U) :
    z.toH1Function.grad = fun x => (z.1.2 x).toVec := rfl

/-- Passing from a quotient graph to its representatives and back is exact. -/
@[simp]
theorem toW1pGraph_toH1Function {d : ℕ} {U : Set (Vec d)} (z : H1Graph U) :
    z.toH1Function.toW1pFunction.toW1pGraph = z := by
  apply Subtype.ext
  apply Prod.ext
  · exact Lp.toLp_coeFn z.1.1 (Lp.memLp z.1.1)
  · exact Lp.toLp_coeFn z.1.2 (Lp.memLp z.1.2)

end H1Graph

end

end PDE
