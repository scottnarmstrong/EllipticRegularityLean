module

public import PDEFoundation.PDE.WeakDivergenceForm

/-! # Common scalar rescaling of divergence-form equations -/

@[expose] public section

namespace PDE

open MeasureTheory

private theorem vecDot_smul_left_scale {d : ℕ} (c : ℝ) (x y : Vec d) :
    vecDot (c • x) y = c * vecDot x y := by
  unfold vecDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Scaling the coefficient, scalar source, and divergence forcing by the same
real number preserves the actual safe weak equation. -/
theorem IsWeakDivergenceFormSolutionOn.smul_coefficient_source_forcing
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F) (c : ℝ) :
    IsWeakDivergenceFormSolutionOn
      (fun x => c • a x) U u (fun x => c * f x) (fun x => c • F x) := by
  intro φ
  have hold := hsol φ
  have hflux : IntegrableOn
      (fun x => vecDot (matVecMul (c • a x) (u.grad x)) (φ.grad x)) U := by
    apply hold.1.flux_integrable.const_mul c |>.congr
    filter_upwards with x
    change c * vecDot ((a x).mulVec (u.grad x)) (φ.grad x) =
      vecDot ((c • a x).mulVec (u.grad x)) (φ.grad x)
    rw [Matrix.smul_mulVec, vecDot_smul_left_scale]
  have hsource : IntegrableOn (fun x => c * f x * φ x) U := by
    apply hold.1.source_integrable.const_mul c |>.congr
    filter_upwards with x
    ring
  have hforcing : IntegrableOn
      (fun x => vecDot (c • F x) (φ.grad x)) U := by
    apply hold.1.forcing_integrable.const_mul c |>.congr
    filter_upwards with x
    rw [vecDot_smul_left_scale]
  refine ⟨⟨hflux, hsource, hforcing⟩, ?_⟩
  have hfluxIntegral :
      (∫ x in U, vecDot (matVecMul (c • a x) (u.grad x)) (φ.grad x)) =
        c * ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    change vecDot ((c • a x).mulVec (u.grad x)) (φ.grad x) =
      c * vecDot ((a x).mulVec (u.grad x)) (φ.grad x)
    rw [Matrix.smul_mulVec, vecDot_smul_left_scale]
  have hsourceIntegral :
      (∫ x in U, c * f x * φ x) = c * ∫ x in U, f x * φ x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hforcingIntegral :
      (∫ x in U, vecDot (c • F x) (φ.grad x)) =
        c * ∫ x in U, vecDot (F x) (φ.grad x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [vecDot_smul_left_scale]
  rw [hfluxIntegral, hsourceIntegral, hforcingIntegral, hold.2]
  ring

end PDE
