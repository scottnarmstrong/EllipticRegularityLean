module

public import PDEFoundation.Measure.LinearVolume
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.WeakDerivative

/-!
# Linear transport of weak test functions

This module records the smooth test-function pullback and its exact derivative
formula under an invertible continuous linear change of variables.
-/

@[expose] public section

namespace PDE

namespace WeakTestFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- Pull a test function on `e '' U` back to `U` along `e`. -/
noncomputable def compLinearEquiv (e : Vec d ≃L[ℝ] Vec d)
    (φ : WeakTestFunction (e '' U)) : WeakTestFunction U where
  toFun := fun x => φ (e x)
  contDiff := φ.contDiff.comp e.contDiff
  hasCompactSupport := by
    show HasCompactSupport (φ.toFun ∘ e.toHomeomorph)
    exact φ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  tsupport_subset := by
    intro x hx
    have hex : e x ∈ tsupport φ.toFun := by
      rw [show (fun y => φ (e y)) = φ.toFun ∘ e.toHomeomorph by rfl,
        tsupport_comp_eq_preimage φ.toFun e.toHomeomorph] at hx
      exact hx
    rcases φ.tsupport_subset hex with ⟨y, hy, hey⟩
    simpa [e.injective hey] using hy

@[simp]
theorem compLinearEquiv_apply (e : Vec d ≃L[ℝ] Vec d)
    (φ : WeakTestFunction (e '' U)) (x : Vec d) :
    φ.compLinearEquiv e x = φ (e x) :=
  rfl

/-- The derivative of a pulled-back test function is the original derivative
precomposed with the linear equivalence. -/
theorem fderiv_compLinearEquiv (e : Vec d ≃L[ℝ] Vec d)
    (φ : WeakTestFunction (e '' U)) (x : Vec d) :
    fderiv ℝ (φ.compLinearEquiv e).toFun x =
      (fderiv ℝ φ.toFun (e x)).comp (e : Vec d →L[ℝ] Vec d) := by
  exact ContinuousLinearEquiv.comp_right_fderiv e

/-- Evaluating the pulled-back derivative in the inverse image of a coordinate
direction recovers that coordinate derivative after the change of variables. -/
theorem fderiv_compLinearEquiv_apply_symm_basisVec
    (e : Vec d ≃L[ℝ] Vec d) (φ : WeakTestFunction (e '' U))
    (x : Vec d) (i : Fin d) :
    (fderiv ℝ (φ.compLinearEquiv e).toFun x) (e.symm (basisVec i)) =
      (fderiv ℝ φ.toFun (e x)) (basisVec i) := by
  rw [fderiv_compLinearEquiv]
  simp

end WeakTestFunction

end PDE
