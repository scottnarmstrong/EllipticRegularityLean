module

public import Mathlib.Probability.CDF
public import PDEFoundation.Measure.NormalizedLp

/-!
# Medians of almost everywhere measurable functions

Existence of a median for a real-valued function on a finite measure space, in the form used in
Step 3 of the Sobolev--Poincaré inequality on normalized convex domains: both `{u ≤ m}` and
`{m ≤ u}` carry at least half of the total mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace PDE

/-- A median of a probability measure on `ℝ`, via its cumulative distribution function. -/
theorem exists_median_real (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    ∃ m : ℝ, Q (Ioi m) ≤ 2⁻¹ ∧ Q (Iio m) ≤ 2⁻¹ := by
  set F := cdf Q with hF
  have hmono : Monotone F := F.mono
  let S : Set ℝ := {t | (2⁻¹ : ℝ) ≤ F t}
  have hne : S.Nonempty := by
    obtain ⟨t, ht⟩ := ((tendsto_cdf_atTop Q).eventually
      (lt_mem_nhds (show (2⁻¹ : ℝ) < 1 by norm_num))).exists
    exact ⟨t, ht.le⟩
  have hbdd : BddBelow S := by
    obtain ⟨t0, ht0⟩ := eventually_atBot.1 ((tendsto_cdf_atBot Q).eventually
      (gt_mem_nhds (show (0 : ℝ) < 2⁻¹ by norm_num)))
    refine ⟨t0, fun s hs => ?_⟩
    by_contra h
    exact absurd (ht0 s (not_le.1 h).le) (not_lt.2 hs)
  set m := sInf S with hm
  have hsucc : ∀ ε > 0, (2⁻¹ : ℝ) ≤ F (m + ε) := by
    intro ε hε
    obtain ⟨s, hs, hsl⟩ := exists_lt_of_csInf_lt hne (show sInf S < m + ε by linarith)
    exact hs.trans (hmono hsl.le)
  have hFm : (2⁻¹ : ℝ) ≤ F m := by
    have hcont : ContinuousWithinAt F (Ici m) m := F.right_continuous m
    have ht : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝[Ici m] m) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 := (tendsto_const_nhds (x := m)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa using h0
      · simp only [mem_Ici, le_add_iff_nonneg_right]
        positivity
    exact ge_of_tendsto (hcont.tendsto.comp ht)
      (Eventually.of_forall fun n => hsucc _ (by positivity))
  have hbelow : ∀ t < m, F t < 2⁻¹ := fun t ht => by
    by_contra h
    exact absurd (csInf_le hbdd (not_lt.1 h)) (not_le.2 ht)
  refine ⟨m, ?_, ?_⟩
  · have h1 : Q.real (Ioi m) = 1 - F m := by
      rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]
    have h2 : Q.real (Ioi m) ≤ 2⁻¹ := by rw [h1]; linarith
    calc Q (Ioi m) = ENNReal.ofReal (Q.real (Ioi m)) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal 2⁻¹ := ENNReal.ofReal_le_ofReal h2
      _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  · have hU : Iio m = ⋃ n : ℕ, Iic (m - 1 / ((n : ℝ) + 1)) := by
      ext t
      simp only [mem_Iio, mem_iUnion, mem_Iic]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < m - t by linarith)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hmonoS : Monotone (fun n : ℕ => Iic (m - 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      refine Iic_subset_Iic.2 ?_
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hT := tendsto_measure_iUnion_atTop (μ := Q) hmonoS
    rw [← hU] at hT
    refine le_of_tendsto' hT fun n => ?_
    have hlt := hbelow (m - 1 / ((n : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
    have : Q.real (Iic (m - 1 / ((n : ℝ) + 1))) ≤ 2⁻¹ := by
      rw [← cdf_eq_real]; exact hlt.le
    calc Q (Iic (m - 1 / ((n : ℝ) + 1)))
        = ENNReal.ofReal (Q.real (Iic (m - 1 / ((n : ℝ) + 1)))) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal 2⁻¹ := ENNReal.ofReal_le_ofReal this
      _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

/-- Median of an a.e. measurable real function on a nonzero finite measure space: each of
`{u ≤ m}` and `{m ≤ u}` carries at least half of the total mass. -/
theorem exists_median {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {u : α → ℝ} (hu : AEMeasurable u μ) :
    ∃ m : ℝ, μ univ ≤ 2 * μ {x | u x ≤ m} ∧ μ univ ≤ 2 * μ {x | m ≤ u x} := by
  have hc0 : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.1 h)
  have hcT : μ univ ≠ ∞ := measure_ne_top _ _
  set c := μ univ with hc
  let P : Measure α := c⁻¹ • μ
  have hPμ : μ = c • P := by
    simp only [P, smul_smul, ENNReal.mul_inv_cancel hc0 hcT, one_smul]
  have : IsProbabilityMeasure P :=
    ⟨by simp only [P, Measure.smul_apply, smul_eq_mul, ← hc]; exact ENNReal.inv_mul_cancel hc0 hcT⟩
  have hPu : AEMeasurable u P := hu.smul_measure c⁻¹
  have : IsProbabilityMeasure (P.map u) := (Measure.isProbabilityMeasure_map_iff hPu).2 inferInstance
  obtain ⟨m, hm1, hm2⟩ := exists_median_real (P.map u)
  rw [Measure.map_apply_of_aemeasurable hPu measurableSet_Ioi] at hm1
  rw [Measure.map_apply_of_aemeasurable hPu measurableSet_Iio] at hm2
  have key : ∀ (s t : Set α), s ∪ t = univ → P t ≤ 2⁻¹ → c ≤ 2 * μ s := by
    intro s t hst ht
    have h1 : c ≤ μ s + μ t := by
      calc c = μ (s ∪ t) := by rw [hst]
        _ ≤ μ s + μ t := measure_union_le _ _
    have h2 : μ t ≤ c / 2 := by
      rw [hPμ]
      simp only [Measure.smul_apply, smul_eq_mul]
      calc c * P t ≤ c * 2⁻¹ := by gcongr
        _ = c / 2 := by rw [div_eq_mul_inv]
    have h3 : c / 2 + c / 2 ≤ μ s + c / 2 := by
      rw [ENNReal.add_halves]; exact h1.trans (by gcongr)
    have h4 : c / 2 ≤ μ s := (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hcT (by norm_num))).1 h3
    calc c = c / 2 + c / 2 := (ENNReal.add_halves c).symm
      _ ≤ μ s + μ s := add_le_add h4 h4
      _ = 2 * μ s := (two_mul _).symm
  refine ⟨m, key _ {x | m < u x} ?_ hm1, key _ {x | u x < m} ?_ hm2⟩
  · ext x; simp [le_or_gt]
  · ext x; simp [le_or_gt]

end PDE
