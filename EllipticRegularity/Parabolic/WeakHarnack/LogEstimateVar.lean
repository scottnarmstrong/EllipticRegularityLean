module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateSliceB

/-!
# Integrability of the variance `V(t) = ∫ |w(·,t) - m(t)|² dν`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem variance_eq_sub {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  have h1 : Integrable f μ := hf.integrable one_le_two
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  set m := ∫ y, f y ∂μ with hm
  have : (fun x => (f x - m) ^ 2) = fun x => f x ^ 2 - 2 * m * f x + m ^ 2 := by
    funext x; ring
  have i3 : Integrable (fun x => f x ^ 2 - 2 * m * f x) μ := h2.sub (h1.const_mul _)
  have e1 := integral_add i3 (integrable_const (μ := μ) (m ^ 2))
  have e2 := integral_sub h2 (h1.const_mul (2 * m))
  have e3 := integral_const_mul (μ := μ) (2 * m) f
  rw [this]
  refine e1.trans ?_
  rw [e2, e3, ← hm]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Integrability of the variance in time. -/
theorem integrable_logV {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s, |deriv G s| ≤ M) {L : NNReal} (hL : LipschitzWith L G)
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    Integrable (fun τ => ∫ x, (G (u.toFun (x, τ)) -
        ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
      (volume.restrict (Ioc (-1 : ℝ) 0)) := by
  have hw := memLp_comp_lipschitz (u := u) hL
  have hf1 := integrable_zeta2_mul (μ := volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ
    Ioc (-1 : ℝ) 0)) hw.integrable_sq
  have hf2 := integrable_zeta2_mul (μ := volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ
    Ioc (-1 : ℝ) 0)) (hw.integrable one_le_two)
  rw [PDE.Parabolic.Energy.volume_restrict_prod] at hf1 hf2
  have hS2 := hf1.integral_prod_right
  have hS1 := hf2.integral_prod_right
  have hZ := cutoffZ_pos d
  have hmeasS1 : AEStronglyMeasurable (fun τ => ∫ x in euclideanBall (0 : Vec d) 1,
      radialCutoff d x ^ 2 * G (u.toFun (x, τ))) (volume.restrict (Ioc (-1 : ℝ) 0)) :=
    hS1.aestronglyMeasurable
  have hgood := logSlice_ae hG hM0 hM u
  have hEq : ∀ᵐ τ ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      ∫ x, (G (u.toFun (x, τ)) - ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2
          ∂(cutoffMeasure d) =
        (cutoffZ d)⁻¹ * (∫ x in euclideanBall (0 : Vec d) 1,
          radialCutoff d x ^ 2 * G (u.toFun (x, τ)) ^ 2) -
        ((cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1,
          radialCutoff d x ^ 2 * G (u.toFun (x, τ))) ^ 2 := by
    filter_upwards [hgood] with τ hτ
    obtain ⟨h, hh, -⟩ := hτ
    have hmem : MemLp (fun x => G (u.toFun (x, τ))) 2 (cutoffMeasure d) := by
      refine memLp_cutoffMeasure ?_
      have := memLp_ball h (R := 1) subset_rfl
      simpa only [funext hh] using this
    rw [variance_eq_sub hmem, integral_cutoffMeasure (fun x => G (u.toFun (x, τ)) ^ 2),
      integral_cutoffMeasure (fun x => G (u.toFun (x, τ)))]
  have hVnn : ∀ τ, 0 ≤ ∫ x, (G (u.toFun (x, τ)) -
      ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d) :=
    fun τ => integral_nonneg fun x => sq_nonneg _
  refine Integrable.mono' (g := fun τ => (cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1,
      radialCutoff d x ^ 2 * G (u.toFun (x, τ)) ^ 2) (hS2.const_mul _) ?_ ?_
  · refine AEStronglyMeasurable.congr (f := fun τ => (cutoffZ d)⁻¹ * (∫ x in
      euclideanBall (0 : Vec d) 1, radialCutoff d x ^ 2 * G (u.toFun (x, τ)) ^ 2) -
        ((cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1,
          radialCutoff d x ^ 2 * G (u.toFun (x, τ))) ^ 2) ?_ (hEq.mono fun τ h => h.symm)
    exact (hS2.aestronglyMeasurable.const_mul _).sub (hmeasS1.const_mul _ |>.pow 2)
  · filter_upwards [hEq] with τ h
    rw [Real.norm_eq_abs, abs_of_nonneg (hVnn τ), h]
    have := sq_nonneg ((cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1,
      radialCutoff d x ^ 2 * G (u.toFun (x, τ)))
    linarith

end PDE.Parabolic.WeakHarnack
