module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateGood

/-!
# The logarithmic estimate for weak supersolutions (hypotheses of `logTail_integrated`)

Main result: `log_tail_supersolution_H3`, with `c = logTailC d` and `K = Λ · logTailK0 d`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem mean_eq_pairing (f : Vec d → ℝ) :
    ∫ x, f x ∂(cutoffMeasure d) =
      (cutoffZ d)⁻¹ * ∫ x in euclideanBall (0 : Vec d) 1, f x * radialCutoff d x ^ 2 := by
  rw [integral_cutoffMeasure]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring

/-- The differential inequality for `w = G ∘ u`, between two good times. -/
theorem logDiff_w {Λ : ℝ} (hΛ : 0 ≤ Λ) {G : ℝ → ℝ}
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    {N₀ N₁ : Set ℝ} (hN₁ : volume N₁ = 0)
    (hQ : Integrable (logQ Λ G u)
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)))
    (hVw : Integrable (fun τ => ∫ x, (G (u.toFun (x, τ)) -
        ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
      (volume.restrict (Ioc (-1 : ℝ) 0)))
    (hA : ∀ s t : ℝ, s ∈ Ioc (-1 : ℝ) 0 → t ∈ Ioc (-1 : ℝ) 0 → s ∉ N₀ → t ∉ N₀ → s < t →
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t, logQ Λ G u z ≤
        (∫ x in euclideanBall (0 : Vec d) 1, G (u.toFun (x, t)) * radialCutoff d x ^ 2) -
          ∫ x in euclideanBall (0 : Vec d) 1, G (u.toFun (x, s)) * radialCutoff d x ^ 2)
    (hgood : ∀ t ∈ Ioc (-1 : ℝ) 0, t ∉ N₁ →
      (∃ h : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x, h.toFun x = G (u.toFun (x, t))) ∧
          ∀ x, h.grad x = deriv G (u.toFun (x, t)) • u.grad (x, t)) ∧
      ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun (x, t))
    {t₁ t₂ : ℝ} (h1 : t₁ ∈ Ioc (-1 : ℝ) 0) (h2 : t₂ ∈ Ioc (-1 : ℝ) 0) (hN1 : t₁ ∉ N₀)
    (hN2 : t₂ ∉ N₀) (hlt : t₁ < t₂) :
    ∫ τ in Ioc t₁ t₂, (logTailC d * (∫ x, (G (u.toFun (x, τ)) -
        ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d)) -
          Λ * logTailK0 d) ≤
      (∫ x, G (u.toFun (x, t₂)) ∂(cutoffMeasure d)) - ∫ x, G (u.toFun (x, t₁)) ∂(cutoffMeasure d) := by
  have hsub : Ioc t₁ t₂ ⊆ Ioc (-1 : ℝ) 0 := Ioc_subset_Ioc h1.1.le h2.2
  have hQ' : IntegrableOn (logQ Λ G u) (euclideanBall (0 : Vec d) 1 ×ˢ Ioc t₁ t₂) :=
    hQ.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hsub) le_rfl)
  obtain ⟨hQslice, hfub⟩ := PDE.Parabolic.WeakSlice.integral_prod_slices hQ'
  have hVint : IntegrableOn (fun τ => ∫ x, (G (u.toFun (x, τ)) -
        ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d)) (Ioc t₁ t₂) :=
    hVw.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hfin : volume (Ioc t₁ t₂) ≠ ⊤ := (measure_Ioc_lt_top).ne
  have hZ := cutoffZ_pos d
  calc ∫ τ in Ioc t₁ t₂, (logTailC d * (∫ x, (G (u.toFun (x, τ)) -
        ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d)) -
          Λ * logTailK0 d)
      ≤ ∫ τ in Ioc t₁ t₂, (cutoffZ d)⁻¹ *
          ∫ x in euclideanBall (0 : Vec d) 1, logQ Λ G u (x, τ) := by
        refine setIntegral_mono_ae_restrict ((hVint.const_mul _).sub
          (integrableOn_const hfin)) (hQslice.const_mul _) ?_
        have hae : ∀ᵐ τ ∂(volume.restrict (Ioc t₁ t₂)), τ ∉ N₁ :=
          ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₁)
        filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with τ hτ hτI
        obtain ⟨⟨h, hh, hg⟩, -⟩ := hgood τ (hsub hτI) hτ
        exact logSlice_lower_Q hΛ u h hh hg
    _ = (cutoffZ d)⁻¹ * ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc t₁ t₂, logQ Λ G u z := by
        rw [hfub, MeasureTheory.integral_const_mul]
    _ ≤ (cutoffZ d)⁻¹ * ((∫ x in euclideanBall (0 : Vec d) 1,
          G (u.toFun (x, t₂)) * radialCutoff d x ^ 2) -
          ∫ x in euclideanBall (0 : Vec d) 1, G (u.toFun (x, t₁)) * radialCutoff d x ^ 2) :=
        mul_le_mul_of_nonneg_left (hA t₁ t₂ h1 h2 hN1 hN2 hlt) (inv_nonneg.2 hZ.le)
    _ = _ := by
        rw [mul_sub, mean_eq_pairing (fun x => G (u.toFun (x, t₂))),
          mean_eq_pairing (fun x => G (u.toFun (x, t₁)))]

end PDE.Parabolic.WeakHarnack
