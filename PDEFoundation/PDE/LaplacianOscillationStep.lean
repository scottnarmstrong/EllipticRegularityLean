module

public import PDEFoundation.PDE.HarmonicCenteredReplacement
public import PDEFoundation.PDE.HarmonicGradientOscillationAllDimensions
public import PDEFoundation.PDE.PerturbationEnergy
public import PDEFoundation.Sobolev.H1.OrthogonalComparison

/-! # One-step harmonic comparison for the weak Laplace equation -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Harmonic replacement gives the exact linear coefficient on the retained
outer excess and the exact square-root volume factor on the forcing error. -/
theorem centeredVectorMeanL2_weakLaplacian_grad_step
    (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall z R) u 0 F)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    centeredVectorMeanL2 (euclideanBall z r) u.grad ≤
      (r / R) * centeredVectorMeanL2 (euclideanBall z R) u.grad +
        (R / r) ^ ((d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (F x))) := by
  obtain ⟨h, w, _hvalue, hgrad, horth, _⟩ :=
    exists_harmonicReplacement_centered_on_euclideanBall hd hR u
  have hRtop : volume (euclideanBall z R) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le)
  have hrtop : volume (euclideanBall z r) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le)
  have hweak : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (h.grad x) (φ.grad x) = 0 := by
    intro φ
    let φ10 := H10Function.ofContDiff (isOpen_euclideanBall z R)
      φ.contDiff φ.hasCompactSupport φ.tsupport_subset
    simpa only [φ10, H10Function.ofContDiff_grad, WeakTestFunction.grad_apply,
      WeakTestFunction.partialDeriv] using! horth φ10
  have hdecay := centeredVectorMeanL2_weakHarmonic_grad_decay_of_pos
    hd hR h hweak hr hrR le_rfl
  have hsum : (fun x => h.grad x + w.toH1Function.grad x) = u.grad := by
    funext x
    rw [congrFun hgrad x]
    exact sub_add_cancel _ _
  have hcomparison := centeredVectorMeanL2_comparison_of_orthogonal_contraction
    (euclideanBall_mono hr.le hrR) h.gradMemL2 w.toH1Function.gradMemL2
    (volume_euclideanBall_pos z hr) hrtop (volume_euclideanBall_pos z hR) hRtop
    (w.vectorIntegralAverage_grad_eq_zero hRtop) (horth w)
    (div_nonneg hr.le hR.le) hdecay
  rw [hsum] at hcomparison
  have hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R),
      IsMatrixPerturbationLE 0 (1 : Mat d) 1 := by
    filter_upwards with x
    intro xi
    simp [matVecMul, vecEuclideanNorm, vecNormSq, vecDot]
  have herror := sqrt_integralAverage_vecNormSq_replacement_error_le
    (a := fun _ => (1 : Mat d))
    (by norm_num : (0 : ℝ) ≤ 0)
    (fun _ _ => aemeasurable_const) hclose hF hsol w
    (by simpa only [hgrad] using horth w)
  simp only [zero_mul, zero_add] at herror
  have hfactor : Real.sqrt ((volume (euclideanBall z R)).toReal /
      (volume (euclideanBall z r)).toReal) = (R / r) ^ ((d : ℝ) / 2) := by
    rw [volume_euclideanBall_toReal_div_eq_div_pow z z hr hR,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (div_nonneg hR.le hr.le)]
    congr 1
    ring
  exact (hcomparison.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left herror (Real.sqrt_nonneg _)))).trans_eq
      (by rw [hfactor])

/-- The one-step excess estimate in the manuscript's scale parameter. -/
theorem centeredVectorMeanL2_weakLaplacian_grad_theta_step
    (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall z R) u 0 F)
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1) :
    centeredVectorMeanL2 (euclideanBall z (θ * R)) u.grad ≤
      θ * centeredVectorMeanL2 (euclideanBall z R) u.grad +
        θ ^ (-(d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (F x))) := by
  have h := centeredVectorMeanL2_weakLaplacian_grad_step hd hR u hF hsol
    (mul_pos hθ hR) (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθone hR.le)
  have hrat : R / (θ * R) = θ⁻¹ := by field_simp
  rw [mul_div_cancel_right₀ θ hR.ne', hrat,
    ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [neg_div] using h

end
end PDE
