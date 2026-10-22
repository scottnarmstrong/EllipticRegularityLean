module

public import PDEFoundation.Euler.TimeDiag

/-!
# Diagonal limit for bilinear time-mollified forms: building blocks

`𝓑ₙ(ω,τ) = ∫ σ ∈ [0,T], η_n(σ-τ) b(ω,σ)` is jointly measurable, bounded by `B`, and converges to `b(ω,τ)`
for a.e. `(ω,τ)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : ℝ} {b : Ω × ℝ → ℝ}

theorem bilin_B_aesm [SFinite μ] (n : ℕ)
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    AEStronglyMeasurable (fun p : Ω × ℝ => ∫ σ, etaK n (σ - p.2) * b (p.1, σ)
      ∂(volume.restrict (Icc (0 : ℝ) T))) (μ.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hq : Measure.QuasiMeasurePreserving (fun q : (Ω × ℝ) × ℝ => (q.1.1, q.2))
      ((μ.prod ν).prod ν) (μ.prod ν) :=
    (QuasiMeasurePreserving.prodMap (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν))
      ((MeasurePreserving.id ν).quasiMeasurePreserving))
  have h1 : AEStronglyMeasurable (fun q : (Ω × ℝ) × ℝ => b (q.1.1, q.2)) ((μ.prod ν).prod ν) :=
    hb.comp_quasiMeasurePreserving hq
  have h2 : AEStronglyMeasurable (fun q : (Ω × ℝ) × ℝ => etaK n (q.2 - q.1.2)) ((μ.prod ν).prod ν) :=
    ((((etaK_contDiff n).continuous.comp (continuous_fst.sub continuous_snd) :
      Continuous (fun r : ℝ × ℝ => etaK n (r.1 - r.2))).stronglyMeasurable).comp_measurable
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).aestronglyMeasurable
  exact (h2.mul h1).integral_prod_right'

theorem bilin_B_bound {B : ℝ} (hB0 : 0 ≤ B) [SFinite μ]
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ τ, |∫ σ, etaK n (σ - τ) * b (ω, σ) ∂(volume.restrict (Icc (0 : ℝ) T))| ≤ B := by
  filter_upwards [hb.prodMk_left, Measure.ae_ae_of_ae_prod hbB] with ω hω hω'
  exact fun τ => abs_timeMollify_le hB0 hω hω' n τ

theorem bilin_B_tendsto {B : ℝ} [SFinite μ]
    (hb : AEStronglyMeasurable b (μ.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hbB : ∀ᵐ p ∂(μ.prod (volume.restrict (Icc (0 : ℝ) T))), |b p| ≤ B) :
    ∀ᵐ ω ∂μ, ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun n => ∫ σ, etaK n (σ - τ) * b (ω, σ) ∂(volume.restrict (Icc (0 : ℝ) T)))
        atTop (𝓝 (b (ω, τ))) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  filter_upwards [hb.prodMk_left, Measure.ae_ae_of_ae_prod hbB] with ω hω hω'
  set f : ℝ → ℝ := (Icc (0 : ℝ) T).indicator (fun σ => b (ω, σ)) with hf
  have hfint : Integrable f volume := by
    rw [hf, integrable_indicator_iff measurableSet_Icc]
    refine Integrable.of_bound (C := B) hω ?_  
    exact hω'
  have hlim := ae_tendsto_timeMollify hfint.locallyIntegrable
  have hconv : ∀ n τ, ∫ σ, etaK n (σ - τ) * f σ = ∫ σ, etaK n (σ - τ) * b (ω, σ) ∂ν := by
    intro n τ
    rw [hν, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only [hf, Set.indicator_apply]
    split_ifs <;> simp
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_Icc] with τ hτ hτm
  have hfτ : f τ = b (ω, τ) := by rw [hf, Set.indicator_of_mem hτm]
  rw [hfτ] at hτ
  exact hτ.congr (fun n => hconv n τ)

end PDE
