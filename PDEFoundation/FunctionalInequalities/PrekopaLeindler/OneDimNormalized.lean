module

public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.LayerCake
public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.OneDimSets

/-!
# One-dimensional Prékopa--Leindler: the normalized case

If `f, g ≤ 1` have supremum `1` and `k (l x + (1-l) y) ≥ f x ^ l * g y ^ (1-l)`, then
`l ∫ f + (1-l) ∫ g ≤ ∫ k`, by the layer-cake formula and one-dimensional Brunn--Minkowski.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- The tail measure `t ↦ μ {x | ofReal t < f x}` is antitone, hence measurable. -/
theorem measurable_tail {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ≥0∞) :
    Measurable fun t : ℝ => μ {x | ENNReal.ofReal t < f x} := by
  refine Antitone.measurable fun s t hst => measure_mono fun x hx => ?_
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- Superlevel sets of `k` contain the weighted sums of superlevel sets of `f` and `g`. -/
theorem superlevel_subset {l : ℝ} {f g k : ℝ → ℝ≥0∞} (hl0 : 0 < l) (hl1 : l < 1) {t : ℝ}
    (ht : 0 < t)
    (hyp : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ k (l • x + (1 - l) • y)) :
    l • {x | ENNReal.ofReal t < f x} + (1 - l) • {x | ENNReal.ofReal t < g x} ⊆
      {x | ENNReal.ofReal t < k x} := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  have hτ0 : ENNReal.ofReal t ≠ 0 := by simpa using ht
  have hτ1 : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  have h1 : ENNReal.ofReal t ^ l < f a ^ l := ENNReal.rpow_lt_rpow ha hl0
  have h2 : ENNReal.ofReal t ^ (1 - l) < g b ^ (1 - l) :=
    ENNReal.rpow_lt_rpow hb (sub_pos.2 hl1)
  have h3 : ENNReal.ofReal t ^ l * ENNReal.ofReal t ^ (1 - l) = ENNReal.ofReal t := by
    rw [← ENNReal.rpow_add _ _ hτ0 hτ1]; simp
  have := ENNReal.mul_lt_mul h1 h2
  rw [h3] at this
  exact lt_of_lt_of_le this (hyp a b)

/-- Normalized one-dimensional Prékopa--Leindler. -/
theorem normalized_oneDim {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g k : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ t : ℝ≥0∞, t < 1 → ∃ x, t < f x) (hgs : ∀ t : ℝ≥0∞, t < 1 → ∃ x, t < g x)
    (hyp : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ k (l • x + (1 - l) • y)) :
    ENNReal.ofReal l * (∫⁻ x, f x) + ENNReal.ofReal (1 - l) * (∫⁻ x, g x) ≤ ∫⁻ x, k x := by
  rw [lintegral_eq_lintegral_volume_lt hf, lintegral_eq_lintegral_volume_lt hg,
    lintegral_eq_lintegral_volume_lt hk,
    ← lintegral_const_mul _ (measurable_tail volume f),
    ← lintegral_const_mul _ (measurable_tail volume g),
    ← lintegral_add_left ((measurable_tail volume f).const_mul _)]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  by_cases ht1 : 1 ≤ t
  · have hA : {x | ENNReal.ofReal t < f x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hf1 x).trans (by simpa using ht1)
    have hB : {x | ENNReal.ofReal t < g x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hg1 x).trans (by simpa using ht1)
    simp [hA, hB]
  · have ht1' : ENNReal.ofReal t < 1 := by
      rw [ENNReal.ofReal_lt_one]; exact not_le.1 ht1
    obtain ⟨a, ha⟩ := hfs _ ht1'
    obtain ⟨b, hb⟩ := hgs _ ht1'
    have hAm : MeasurableSet {x | ENNReal.ofReal t < f x} := measurableSet_lt measurable_const hf
    have hBm : MeasurableSet {x | ENNReal.ofReal t < g x} := measurableSet_lt measurable_const hg
    calc _ ≤ volume (l • {x | ENNReal.ofReal t < f x} + (1 - l) • {x | ENNReal.ofReal t < g x}) :=
          volume_smul_add_smul hl0 hl1 hAm hBm ⟨a, ha⟩ ⟨b, hb⟩
      _ ≤ _ := measure_mono (superlevel_subset hl0 hl1 ht0 hyp)

end PDE.PrekopaLeindlerProof
