module

public import PDEFoundation.Euler.TimeDiagLimit

/-!
# Integrability of bilinear time forms

For `a`, `b` bounded and jointly a.e. strongly measurable on `μ ⊗ Leb|[0,T]` with `μ` finite,
`(τ,σ) ↦ ∫ a(ω,τ) b(ω,σ) dμ` is integrable on `[0,T]²`; and for `d ∈ L¹(μ)` the datum form
`σ ↦ ∫ d(ω) b(ω,σ) dμ` is integrable on `[0,T]`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : ℝ} {a b : Ω × ℝ → ℝ}

theorem bilin_integrable [IsFiniteMeasure μ] {A B : ℝ} (hA0 : 0 ≤ A)
    (ha : AEStronglyMeasurable a (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (haA : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |a p| ≤ A)
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B) :
    Integrable (fun r : ℝ × ℝ => ∫ ω, a (ω, r.1) * b (ω, r.2) ∂μ)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hqa : Measure.QuasiMeasurePreserving (fun q : (ℝ × ℝ) × Ω => (q.2, q.1.1))
      ((ν.prod ν).prod μ) (μ.prod ν) := by
    have h1 : Measure.QuasiMeasurePreserving (fun q : (ℝ × ℝ) × Ω => (q.1.1, q.2))
        ((ν.prod ν).prod μ) (ν.prod μ) :=
      QuasiMeasurePreserving.prodMap (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν))
        (MeasurePreserving.id μ).quasiMeasurePreserving
    exact (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.comp h1
  have hqb : Measure.QuasiMeasurePreserving (fun q : (ℝ × ℝ) × Ω => (q.2, q.1.2))
      ((ν.prod ν).prod μ) (μ.prod ν) := by
    have h1 : Measure.QuasiMeasurePreserving (fun q : (ℝ × ℝ) × Ω => (q.1.2, q.2))
        ((ν.prod ν).prod μ) (ν.prod μ) :=
      QuasiMeasurePreserving.prodMap (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν))
        (MeasurePreserving.id μ).quasiMeasurePreserving
    exact (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.comp h1
  have hmeas : AEStronglyMeasurable (fun q : (ℝ × ℝ) × Ω => a (q.2, q.1.1) * b (q.2, q.1.2))
      ((ν.prod ν).prod μ) :=
    (ha.comp_quasiMeasurePreserving hqa).mul (hb.comp_quasiMeasurePreserving hqb)
  refine Integrable.of_bound (C := μ.real univ * A * B) hmeas.integral_prod_right' ?_
  have hτ : ∀ᵐ τ ∂ν, ∀ᵐ ω ∂μ, |a (ω, τ)| ≤ A := by
    have h1 := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae haA
    exact Measure.ae_ae_of_ae_prod h1
  have hσ : ∀ᵐ σ ∂ν, ∀ᵐ ω ∂μ, |b (ω, σ)| ≤ B := by
    have h1 := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hbB
    exact Measure.ae_ae_of_ae_prod h1
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hτ
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hσ
  filter_upwards [h1, h2] with r hr1 hr2
  have hbd : ∀ᵐ ω ∂μ, ‖a (ω, r.1) * b (ω, r.2)‖ ≤ A * B := by
    filter_upwards [hr1, hr2] with ω h1 h2
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hA0
  calc ‖∫ ω, a (ω, r.1) * b (ω, r.2) ∂μ‖ ≤ A * B * μ.real univ := norm_integral_le_of_norm_le_const hbd
    _ = μ.real univ * A * B := by ring

/-- Datum forms: `σ ↦ ∫ d(ω) b(ω,σ)` is integrable on `[0,T]` for `d ∈ L¹(μ)`, `b` bounded. -/
theorem datum_integrable [IsFiniteMeasure μ] {B : ℝ} {d : Ω → ℝ} (hd : Integrable d μ)
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B) :
    Integrable (fun σ => ∫ ω, d ω * b (ω, σ) ∂μ) (volume.restrict (Icc (0 : ℝ) T)) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hint : Integrable (fun p : Ω × ℝ => d p.1 * b p) (μ.prod ν) := by
    refine Integrable.mono' (((hd.norm).comp_fst ν).mul_const |B|) ?_ ?_
    · exact (hd.aestronglyMeasurable.comp_fst).mul hb
    · filter_upwards [hbB] with p hp
      rw [norm_mul, ← Real.norm_eq_abs (b p)] at *
      rw [Real.norm_eq_abs] at hp
      exact mul_le_mul_of_nonneg_left (hp.trans (le_abs_self B)) (norm_nonneg _)
  exact hint.integral_prod_right

end PDE
