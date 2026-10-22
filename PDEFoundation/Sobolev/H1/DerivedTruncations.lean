module

public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.H1.Truncation

/-!
# Derived one-sided truncations in `H¹`

This module is the exact `p = 2` representative-level facade for the
one-sided truncations derived from the existing `H¹` negation and positive
part APIs.  It mirrors the `W^{1,p}` organization while retaining literal
value and gradient representatives.
-/

@[expose] public section

namespace PDE

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The negative part relative to `k`, namely `(k-u)₊`. -/
noncomputable def negativePartConstSub
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (k : ℝ) : H1Function U :=
  (-u).positivePartSubConst hU (-k)

@[simp]
theorem negativePartConstSub_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (k : ℝ) :
    (u.negativePartConstSub hU k).toFun =
      fun x => max (k - u.toFun x) 0 := by
  funext x
  rw [negativePartConstSub, positivePartSubConst_toFun, neg_toFun]
  ring_nf

@[simp]
theorem negativePartConstSub_grad
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (k : ℝ) :
    (u.negativePartConstSub hU k).grad =
      fun x => {y | u.toFun y < k}.indicator (-u.grad) x := by
  funext x
  rw [negativePartConstSub, positivePartSubConst_grad, neg_toFun, neg_grad]
  by_cases hx : u.toFun x < k
  · have hx' : -k < -u.toFun x := by linarith
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx, ite_eq_left hx',
      Pi.neg_apply]
  · have hx' : ¬ -k < -u.toFun x := by
      simp only [not_lt] at hx ⊢
      linarith
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx, ite_eq_right hx']

end H1Function

end PDE
