module

public import PDEFoundation.Euler.Osgood

/-!
# Global Osgood vanishing on `[0, T]`

A continuous nonnegative `y ≤ B²` on `[0, T]` satisfying the Yudovich integral inequality from
time `0` for all `p ≥ 2` vanishes on all of `[0, T]`: the local window of `osgood_yudovich` is
restarted in steps of length `1 / (2 (K + 1))`; vanishing on `[0, s]` makes the integral from
`0` equal to the integral from `s`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

/-- Global Osgood vanishing on `[0, T]` (restart at the end of each window). -/
theorem osgood_yudovich_global {y : ℝ → ℝ} {T K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hyc : ContinuousOn y (Icc 0 T))
    (hy0 : ∀ t ∈ Icc 0 T, 0 ≤ y t) (hyB : ∀ t ∈ Icc 0 T, y t ≤ B ^ 2)
    (h : ∀ p : ℝ, 2 ≤ p → ∀ t ∈ Icc 0 T,
      y t ≤ ∫ τ in (0 : ℝ)..t, K * p * B ^ (2 / p) * y τ ^ (1 - 1 / p)) :
    ∀ t ∈ Icc 0 T, y t = 0 := by
  have hδ : 0 < 1 / (2 * (K + 1)) := by positivity
  set δ : ℝ := 1 / (2 * (K + 1)) with hδdef
  have hKδ : K * δ ≤ 1 / 2 := by
    rw [hδdef, mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hint : ∀ p : ℝ, 2 ≤ p → ∀ a b : ℝ, a ∈ Icc 0 T → b ∈ Icc 0 T →
      IntervalIntegrable (fun τ => K * p * B ^ (2 / p) * y τ ^ (1 - 1 / p)) volume a b := by
    intro p hp a b ha hb
    have hsub : uIcc a b ⊆ Icc 0 T := Set.uIcc_subset_Icc ha hb
    have hp0 : 0 < p := by linarith
    have he : 0 ≤ 1 - 1 / p := by
      have : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
      linarith
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul ((hyc.mono hsub).rpow_const fun x _ => Or.inr he)
  have key : ∀ n : ℕ, ∀ t ∈ Icc 0 T, t ≤ n * δ → y t = 0 := by
    intro n
    induction n with
    | zero =>
      intro t ht htn
      have h0 : t = 0 := le_antisymm (by simpa using htn) ht.1
      subst h0
      have h1 := h 2 le_rfl 0 ht
      simp only [intervalIntegral.integral_same] at h1
      exact le_antisymm h1 (hy0 0 ht)
    | succ n ih =>
      intro t ht htn
      by_cases hle : t ≤ n * δ
      · exact ih t ht hle
      · rw [not_le] at hle
        have hs0 : 0 ≤ (n : ℝ) * δ := by positivity
        have hsT : (n : ℝ) * δ ≤ T := hle.le.trans ht.2
        have hsIcc : (n : ℝ) * δ ∈ Icc 0 T := ⟨hs0, hsT⟩
        have hos := osgood_yudovich (s := (n : ℝ) * δ) (t₀ := T) (K := K) (B := B) hK hB
          (fun t ht => hy0 t ⟨hs0.trans ht.1, ht.2⟩) (fun t ht => hyB t ⟨hs0.trans ht.1, ht.2⟩)
          ((hyc.mono (Icc_subset_Icc_left hs0)).intervalIntegrable_of_Icc hsT)
          (by
            intro p hp t htt
            have htI : t ∈ Icc 0 T := ⟨hs0.trans htt.1, htt.2⟩
            have h1 := h p hp t htI
            rw [← intervalIntegral.integral_add_adjacent_intervals (hint p hp 0 _ ⟨le_rfl, hsIcc.1.trans hsT⟩ hsIcc)
              (hint p hp _ t hsIcc htI)] at h1
            have hz : ∫ τ in (0 : ℝ)..(n : ℝ) * δ, K * p * B ^ (2 / p) * y τ ^ (1 - 1 / p) = 0 := by
              have hz0 : ∫ τ in (0 : ℝ)..(n : ℝ) * δ, (0 : ℝ) = 0 := by simp
              refine Eq.trans (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun τ hτ => ?_) hz0
              rw [uIcc_of_le hs0] at hτ
              have hy : y τ = 0 := ih τ ⟨hτ.1, hτ.2.trans hsT⟩ hτ.2
              have hne : (1 - 1 / p) ≠ 0 := by
                have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
                intro h0; linarith
              rw [hy, Real.zero_rpow hne, mul_zero]
            rw [hz, zero_add] at h1
            exact h1)
        refine hos t ⟨hle.le, ht.2⟩ ?_
        have : t - (n : ℝ) * δ ≤ δ := by push_cast at htn; linarith
        exact (mul_le_mul_of_nonneg_left this hK).trans hKδ
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (T / δ)
  exact key n t ht (ht.2.trans ((div_le_iff₀ hδ).1 hn))

end PDE
