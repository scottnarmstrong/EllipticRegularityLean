module

public import PDEFoundation.Measure.DirectedLpBound

/-! # Countable `Lᵖ` gluing on disjoint supports -/

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped ENNReal

noncomputable section

variable {α ρ : Type*}

/-- On pairwise disjoint supports, the positive power of a countable sum is
the sum of the positive powers. -/
theorem tsum_rpow_eq_tsum_rpow_of_pairwiseDisjoint
    (U : ρ → Set α) (hU : Pairwise (Disjoint on U))
    (f : ρ → α → ENNReal)
    (hf0 : ∀ i x, x ∉ U i → f i x = 0)
    {p : ℝ} (hp : 0 < p) (x : α) :
    (∑' i, f i x) ^ p = ∑' i, (f i x) ^ p := by
  by_cases hex : ∃ i, f i x ≠ 0
  · obtain ⟨i, hi⟩ := hex
    have hxi : x ∈ U i := by
      by_contra hxi
      exact hi (hf0 i x hxi)
    have hzero : ∀ j, j ≠ i → f j x = 0 := by
      intro j hji
      by_contra hj
      have hxj : x ∈ U j := by
        by_contra hxj
        exact hj (hf0 j x hxj)
      exact (Set.disjoint_left.mp (hU hji)) hxj hxi
    rw [tsum_eq_single i hzero]
    rw [tsum_eq_single i]
    intro j hji
    rw [hzero j hji, ENNReal.zero_rpow_of_pos hp]
  · push Not at hex
    simp only [hex, tsum_zero, ENNReal.zero_rpow_of_pos hp]

/-- Exact moment decomposition for a countable family of measurable
nonnegative functions with pairwise disjoint supports. -/
theorem lintegral_tsum_rpow_eq_tsum_lintegral_rpow
    [MeasurableSpace α] [Countable ρ]
    (μ : Measure α) (U : ρ → Set α) (hU : Pairwise (Disjoint on U))
    (f : ρ → α → ENNReal) (hf : ∀ i, Measurable (f i))
    (hf0 : ∀ i x, x ∉ U i → f i x = 0)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, (∑' i, f i x) ^ p ∂μ) =
      ∑' i, ∫⁻ x, (f i x) ^ p ∂μ := by
  calc
    (∫⁻ x, (∑' i, f i x) ^ p ∂μ) =
        ∫⁻ x, ∑' i, (f i x) ^ p ∂μ := by
          apply lintegral_congr
          intro x
          exact tsum_rpow_eq_tsum_rpow_of_pairwiseDisjoint U hU f hf0 hp x
    _ = _ := lintegral_tsum fun i => ((hf i).pow_const p).aemeasurable

private theorem eLpNorm_ennreal_eq_moment_rpow
    [MeasurableSpace α]
    (μ : Measure α) (f : α → ENNReal) (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ =
      (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]
  simp only [enorm_eq_self]

/-- Uniform rootwise `Lᵖ` estimates glue across countably many disjoint
measurable supports with exactly the same coefficient. -/
theorem eLpNorm_tsum_le_of_pairwiseDisjoint
    [MeasurableSpace α] [Countable ρ]
    (μ : Measure α) (U : ρ → Set α) (hUmeas : ∀ i, MeasurableSet (U i))
    (hU : Pairwise (Disjoint on U))
    (f : ρ → α → ENNReal) (hf : ∀ i, Measurable (f i))
    (hf0 : ∀ i x, x ∉ U i → f i x = 0)
    (b : α → ENNReal)
    {p : ℝ} (hp : 0 < p) (K : ENNReal)
    (hbound : ∀ i,
      eLpNorm (f i) (ENNReal.ofReal p) μ ≤
        K * eLpNorm b (ENNReal.ofReal p) (μ.restrict (U i))) :
    eLpNorm (fun x => ∑' i, f i x) (ENNReal.ofReal p) μ ≤
      K * eLpNorm b (ENNReal.ofReal p) μ := by
  by_cases hb : AEStronglyMeasurable b μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hb]
    rcases eq_or_ne K 0 with rfl | hK
    · have hp0 : ENNReal.ofReal p ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]
        exact not_le.mpr hp
      have hzero (i : ρ) : f i =ᵐ[μ] 0 :=
        (eLpNorm_eq_zero_iff hp0).1 (le_antisymm (by simpa using hbound i) bot_le)
      have hsum : (fun x => ∑' i, f i x) =ᵐ[μ] 0 := by
        filter_upwards [ae_all_iff.2 hzero] with x hx
        simp [hx]
      rw [eLpNorm_congr_ae hsum]
      simp
    · rw [ENNReal.mul_top hK]
      exact le_top
  let M : (α → ENNReal) → Measure α → ENNReal := fun g ν =>
    ∫⁻ x, (g x) ^ p ∂ν
  have hmomentF : M (fun x => ∑' i, f i x) μ = ∑' i, M (f i) μ :=
    lintegral_tsum_rpow_eq_tsum_lintegral_rpow μ U hU f hf hf0 hp
  have hmomentBound (i : ρ) : M (f i) μ ≤ K ^ p * M b (μ.restrict (U i)) := by
    have hpow := ENNReal.rpow_le_rpow (hbound i) hp.le
    rw [eLpNorm_ennreal_eq_moment_rpow μ (f i) (hf i).aestronglyMeasurable hp,
      eLpNorm_ennreal_eq_moment_rpow (μ.restrict (U i)) b hb.restrict hp,
      ← ENNReal.rpow_mul, show (1 / p) * p = 1 by field_simp,
      ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      ← ENNReal.rpow_mul, show (1 / p) * p = 1 by field_simp,
      ENNReal.rpow_one] at hpow
    exact hpow
  have hsumB : (∑' i, M b (μ.restrict (U i))) ≤ M b μ := by
    rw [← lintegral_iUnion hUmeas hU (fun x => (b x) ^ p)]
    simpa only [M, Measure.restrict_univ] using
      (lintegral_mono_set (μ := μ) (f := fun x => (b x) ^ p)
        (Set.subset_univ (⋃ i, U i)))
  have hmoment : M (fun x => ∑' i, f i x) μ ≤ K ^ p * M b μ := by
    rw [hmomentF]
    calc
      (∑' i, M (f i) μ) ≤ ∑' i, K ^ p * M b (μ.restrict (U i)) :=
        ENNReal.tsum_le_tsum hmomentBound
      _ = K ^ p * ∑' i, M b (μ.restrict (U i)) := ENNReal.tsum_mul_left
      _ ≤ K ^ p * M b μ := mul_le_mul_right hsumB _
  rw [eLpNorm_ennreal_eq_moment_rpow μ _ (Measurable.tsum hf).aestronglyMeasurable hp,
    eLpNorm_ennreal_eq_moment_rpow μ b hb hp]
  have hroot := ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hp.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
    ← ENNReal.rpow_mul, show p * (1 / p) = 1 by field_simp,
    ENNReal.rpow_one] at hroot
  exact hroot

end

end PDE
