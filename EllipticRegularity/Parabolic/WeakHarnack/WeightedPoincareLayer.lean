module

public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincareVariational
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Layer-cake monotonicity for weights in `[0,1]`

If `0 ≤ ρ ≤ 1` is measurable and `∫_{ρ>s} F ≤ C ∫_{ρ>s} G` for every `s ∈ [0,1)`,
then `∫ F ρ ≤ C ∫ G ρ`.  This is the layer-cake formula
`∫ F ρ = ∫₀¹ ∫_{ρ>s} F ds`, integrated against the pointwise comparison.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Layer-cake formula in `[0,∞]`. -/
theorem lintegral_mul_ofReal_weight [SFinite μ] {H : α → ℝ≥0∞} (hH : AEMeasurable H μ)
    {ρ : α → ℝ} (hρm : Measurable ρ) (hρ1 : ∀ x, ρ x ≤ 1) :
    ∫⁻ x, H x * ENNReal.ofReal (ρ x) ∂μ =
      ∫⁻ s in Ico (0 : ℝ) 1, ∫⁻ x in {x | s < ρ x}, H x ∂μ := by
  have hset : MeasurableSet {p : α × ℝ | p.2 < ρ p.1} :=
    measurableSet_lt measurable_snd (hρm.comp measurable_fst)
  have hind : ∀ x, ENNReal.ofReal (ρ x) =
      ∫⁻ s in Ico (0 : ℝ) 1, (Iio (ρ x)).indicator (fun _ => (1 : ℝ≥0∞)) s := by
    intro x
    rw [lintegral_indicator_const measurableSet_Iio,
      Measure.restrict_apply measurableSet_Iio]
    have : Iio (ρ x) ∩ Ico 0 1 = Ico 0 (ρ x) := by
      ext s
      simp only [mem_inter_iff, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, lt_of_lt_of_le h2 (hρ1 x)⟩
    rw [this, Real.volume_Ico]; simp
  have hmeas : AEMeasurable (Function.uncurry fun (x : α) (s : ℝ) =>
      H x * (Iio (ρ x)).indicator (fun _ => (1 : ℝ≥0∞)) s) (μ.prod (volume.restrict (Ico 0 1))) := by
    have h1 : AEMeasurable (fun p : α × ℝ => H p.1) (μ.prod (volume.restrict (Ico 0 1))) :=
      hH.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : Measurable (fun p : α × ℝ =>
        (Iio (ρ p.1)).indicator (fun _ => (1 : ℝ≥0∞)) p.2) := by
      have : (fun p : α × ℝ => (Iio (ρ p.1)).indicator (fun _ => (1 : ℝ≥0∞)) p.2) =
          ({p : α × ℝ | p.2 < ρ p.1}).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext p; simp [Set.indicator]
      rw [this]
      exact measurable_const.indicator hset
    exact h1.mul h2.aemeasurable
  calc ∫⁻ x, H x * ENNReal.ofReal (ρ x) ∂μ
      = ∫⁻ x, (∫⁻ s in Ico (0 : ℝ) 1,
          H x * (Iio (ρ x)).indicator (fun _ => (1 : ℝ≥0∞)) s) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [hind x, lintegral_const_mul'' _ ?_]
        exact (measurable_const.indicator measurableSet_Iio).aemeasurable
    _ = ∫⁻ s in Ico (0 : ℝ) 1, ∫⁻ x,
          H x * (Iio (ρ x)).indicator (fun _ => (1 : ℝ≥0∞)) s ∂μ :=
        lintegral_lintegral_swap hmeas
    _ = _ := by
        refine lintegral_congr fun s => ?_
        rw [← lintegral_indicator (measurableSet_lt measurable_const hρm)]
        refine lintegral_congr fun x => ?_
        by_cases h : s < ρ x <;> simp [Set.indicator, h]

/-- Layer-cake monotonicity. -/
theorem layerCake_mono [IsFiniteMeasure μ] {F G ρ : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x) (hF : Integrable F μ) (hG : Integrable G μ)
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    (h : ∀ s ∈ Ico (0 : ℝ) 1,
      ∫ x in {x | s < ρ x}, F x ∂μ ≤ C * ∫ x in {x | s < ρ x}, G x ∂μ) :
    ∫ x, F x * ρ x ∂μ ≤ C * ∫ x, G x * ρ x ∂μ := by
  have hFρ := integrable_mul_weight hF hρm hρ0 hρ1
  have hGρ := integrable_mul_weight hG hρm hρ0 hρ1
  have hnnF : 0 ≤ᵐ[μ] fun x => F x * ρ x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (hF0 x) (hρ0 x)
  have hnnG : 0 ≤ᵐ[μ] fun x => G x * ρ x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (hG0 x) (hρ0 x)
  have hFm : AEMeasurable (fun x => ENNReal.ofReal (F x)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hF.aemeasurable
  have hGm : AEMeasurable (fun x => ENNReal.ofReal (G x)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hG.aemeasurable
  have hlev : ∀ (K : α → ℝ), (∀ x, 0 ≤ K x) → Integrable K μ → ∀ s : ℝ,
      ENNReal.ofReal (∫ x in {x | s < ρ x}, K x ∂μ) =
        ∫⁻ x in {x | s < ρ x}, ENNReal.ofReal (K x) ∂μ := fun K hK0 hK s =>
    ofReal_integral_eq_lintegral_ofReal hK.restrict (Filter.Eventually.of_forall hK0)
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun x => mul_nonneg (hG0 x) (hρ0 x)))]
  calc ENNReal.ofReal (∫ x, F x * ρ x ∂μ)
      = ∫⁻ x, ENNReal.ofReal (F x) * ENNReal.ofReal (ρ x) ∂μ := by
        rw [ofReal_integral_eq_lintegral_ofReal hFρ hnnF]
        exact lintegral_congr fun x => ENNReal.ofReal_mul (hF0 x)
    _ = ∫⁻ s in Ico (0 : ℝ) 1, ∫⁻ x in {x | s < ρ x}, ENNReal.ofReal (F x) ∂μ :=
        lintegral_mul_ofReal_weight hFm hρm hρ1
    _ ≤ ∫⁻ s in Ico (0 : ℝ) 1, ENNReal.ofReal C *
          ∫⁻ x in {x | s < ρ x}, ENNReal.ofReal (G x) ∂μ := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Ico]
        refine Filter.Eventually.of_forall fun s hs => ?_
        rw [← hlev F hF0 hF s, ← hlev G hG0 hG s, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (h s hs)
    _ = ENNReal.ofReal C * ∫⁻ s in Ico (0 : ℝ) 1,
          ∫⁻ x in {x | s < ρ x}, ENNReal.ofReal (G x) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) * ENNReal.ofReal (ρ x) ∂μ := by
        rw [lintegral_mul_ofReal_weight hGm hρm hρ1]
    _ = ENNReal.ofReal (C * ∫ x, G x * ρ x ∂μ) := by
        rw [ENNReal.ofReal_mul hC, ofReal_integral_eq_lintegral_ofReal hGρ hnnG]
        congr 1
        exact lintegral_congr fun x => (ENNReal.ofReal_mul (hG0 x)).symm

end PDE.Parabolic.WeakHarnack
