module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.HarmonicSmoothing

/-!
# Consequences of the identity-coefficient weak equation

The identity-coefficient equation with zero data is the native weak
harmonicity condition used by the convolution API.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- An identity-coefficient weak solution with zero data satisfies the
variational weak-harmonicity identity for every bundled test function. -/
theorem IsWeakDivergenceFormSolutionOn.identityCoefficient_test_eq_zero
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) U u 0 0)
    (φ : WeakTestFunction U) :
    ∫ x in U, vecDot (u.grad x) (φ.grad x) = 0 := by
  have hmat (x : Vec d) : matVecMul (1 : Mat d) (u.grad x) = u.grad x := by
    change (1 : Mat d).mulVec (u.grad x) = u.grad x
    exact Matrix.one_mulVec _
  calc
    ∫ x in U, vecDot (u.grad x) (φ.grad x) =
        ∫ x in U, vecDot (matVecMul (1 : Mat d) (u.grad x)) (φ.grad x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hmat]
    _ = 0 := by
      simpa [vecDot] using (hsol φ).2

/-- The scalar distributional Laplacian pairing vanishes for an
identity-coefficient weak solution with zero data. -/
theorem IsWeakDivergenceFormSolutionOn.integral_mul_laplacian_eq_zero
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) U u 0 0)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U) :
    ∫ x in U, u.toFun x * euclideanCoordLaplacian ψ x = 0 := by
  exact integral_mul_laplacian_eq_zero_of_weakHarmonic u
    (by
      intro ψ hψ hψc hψs
      exact hsol.identityCoefficient_test_eq_zero ⟨ψ, hψ, hψc, hψs⟩)
    ψ hψ hψc hψs

end PDE
