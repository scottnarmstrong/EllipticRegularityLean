module

public import EllipticRegularity.Parabolic.LocalMax.PowerFamily

/-!
# Structural inequalities for the truncated power family

For `p > 1`, `ε > 0`, `N ≥ 0` the functions `powF p ε N`, `powG p ε N` satisfy, on `s ≥ 0`, with
`K = 2 + p/(p-1)`, the inequalities `F'² ≤ K F'' F`, `G² ≤ K F`, `G'² ≤ K F''`.  The proof splits
into the uncapped region and the quadratic/affine region beyond the cap; in each, the powers are
abstracted to polynomial data before any inequality is proved.
-/

@[expose] public section

namespace PDE.Parabolic.LocalMax

noncomputable section

/-- Polynomial inequalities in the uncapped region. -/
theorem struct_ineqs_uncapped {p K a β w : ℝ} (hp : 1 < p) (hK : K * (p - 1) = 3 * p - 2)
    (hK2 : 2 ≤ K) (ha : 0 < a) (hβ : β ^ 2 = a) (hw : 0 < w) :
    (p * (a * w)) ^ 2 ≤ K * (p * (p - 1) * a) * (a * w ^ 2) ∧
      (β * w) ^ 2 ≤ K * (a * w ^ 2) ∧ (p / 2 * β) ^ 2 ≤ K * (p * (p - 1) * a) := by
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have e : K * (p * (p - 1) * a) * (a * w ^ 2) - (p * (a * w)) ^ 2 =
        p * a ^ 2 * w ^ 2 * (2 * p - 2) := by
      linear_combination (p * a ^ 2 * w ^ 2) * hK
    have : 0 ≤ p * a ^ 2 * w ^ 2 * (2 * p - 2) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · have e : (β * w) ^ 2 = a * w ^ 2 := by rw [mul_pow, hβ]
    have h0 : 0 ≤ a * w ^ 2 := by positivity
    linarith [mul_nonneg (sub_nonneg.2 (by linarith : (1 : ℝ) ≤ K)) h0]
  · have e : K * (p * (p - 1) * a) - (p / 2 * β) ^ 2 = p * a * (11 * p / 4 - 2) := by
      linear_combination (p * a) * hK - (p ^ 2 / 4) * hβ
    have : 0 ≤ p * a * (11 * p / 4 - 2) := mul_nonneg (by positivity) (by linarith)
    linarith

/-- Polynomial inequalities in the quadratic/affine region beyond the cap. -/
theorem struct_ineqs_capped {p K A β L x : ℝ} (hp : 2 < p) (hK : K * (p - 1) = 3 * p - 2)
    (hK2 : 2 ≤ K) (hA : 0 < A) (hβ : β ^ 2 = A) (hL : 0 < L) (hx : 0 ≤ x) :
    (p * A * L + p * (p - 1) * A * x) ^ 2 ≤
        K * (p * (p - 1) * A) * (A * L ^ 2 + p * A * L * x + p * (p - 1) * A * x ^ 2 / 2) ∧
      (β * L + p / 2 * β * x) ^ 2 ≤
        K * (A * L ^ 2 + p * A * L * x + p * (p - 1) * A * x ^ 2 / 2) ∧
      (p / 2 * β) ^ 2 ≤ K * (p * (p - 1) * A) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have e : K * (p * (p - 1) * A) *
          (A * L ^ 2 + p * A * L * x + p * (p - 1) * A * x ^ 2 / 2) -
          (p * A * L + p * (p - 1) * A * x) ^ 2 =
        p * A ^ 2 * ((2 * p - 2) * L ^ 2 + p ^ 2 * L * x + p ^ 2 * (p - 1) * x ^ 2 / 2) := by
      linear_combination
        (p * A * (A * L ^ 2 + p * A * L * x + p * (p - 1) * A * x ^ 2 / 2)) * hK
    have : 0 ≤ p * A ^ 2 * ((2 * p - 2) * L ^ 2 + p ^ 2 * L * x + p ^ 2 * (p - 1) * x ^ 2 / 2) :=
      mul_nonneg (by positivity)
        (add_nonneg (add_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity))
          (by positivity))
    linarith
  · have e : (A * L ^ 2 + p * A * L * x + p * (p - 1) * A * x ^ 2 / 2) -
          (β * L + p / 2 * β * x) ^ 2 = A * x ^ 2 * (p * (p - 2) / 4) := by
      linear_combination (-(L + p / 2 * x) ^ 2) * hβ
    have h1 : 0 ≤ A * x ^ 2 * (p * (p - 2) / 4) :=
      mul_nonneg (by positivity)
        (div_nonneg (mul_nonneg hp0.le (by linarith)) (by norm_num))
    have hF : 0 ≤ A * L ^ 2 + p * A * L * x + p * (p - 1) * A * x ^ 2 / 2 := by positivity
    linarith [mul_nonneg (sub_nonneg.2 (by linarith : (1 : ℝ) ≤ K)) hF]
  · have e : K * (p * (p - 1) * A) - (p / 2 * β) ^ 2 = p * A * (11 * p / 4 - 2) := by
      linear_combination (p * A) * hK - (p ^ 2 / 4) * hβ
    have : 0 ≤ p * A * (11 * p / 4 - 2) := mul_nonneg (by positivity) (by linarith)
    linarith

/-- Rewriting helper: `w ^ (p - 1) = w ^ (p - 2) * w`, `w ^ p = w ^ (p - 2) * w ^ 2`. -/
theorem rpow_split {w : ℝ} (hw : 0 < w) (p : ℝ) :
    w ^ (p - 1) = w ^ (p - 2) * w ∧ w ^ p = w ^ (p - 2) * w ^ 2 ∧
      w ^ (p / 2) = w ^ (p / 2 - 1) * w ∧ (w ^ (p / 2 - 1)) ^ 2 = w ^ (p - 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_add_one hw.ne']; ring_nf
  · rw [show w ^ (2 : ℕ) = w ^ (2 : ℝ) from (Real.rpow_natCast w 2).symm,
      ← Real.rpow_add hw]; ring_nf
  · rw [← Real.rpow_add_one hw.ne']; ring_nf
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]; ring_nf

theorem exists_truncatedPower {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) (N : ℝ) (hN : 0 ≤ N) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ (∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C) ∧
      ContDiff ℝ 1 G ∧ (∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv G s| ≤ M) ∧
      ∀ s, 0 ≤ s →
        0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
        deriv F s ^ 2 ≤ (2 + p / (p - 1)) * deriv (deriv F) s * F s ∧
        G s ^ 2 ≤ (2 + p / (p - 1)) * F s ∧
        deriv G s ^ 2 ≤ (2 + p / (p - 1)) * deriv (deriv F) s ∧
        F s ≤ (s + ε) ^ p ∧ 0 ≤ G s ∧ (s ≤ N → G s = (s + ε) ^ (p / 2)) := by
  have hp1 : 0 < p - 1 := by linarith
  have hK : (2 + p / (p - 1)) * (p - 1) = 3 * p - 2 := by field_simp; ring
  have hK2 : 2 ≤ 2 + p / (p - 1) := by
    have : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hp1.le
    linarith
  refine ⟨powF p ε N, powG p ε N, powF_contDiff hε hN, exists_powF2_bound hp hε hN,
    powG_contDiff hε hN, exists_powG1_bound hp hε hN, fun s hs => ?_⟩
  have key : powF1 p ε N s ^ 2 ≤ (2 + p / (p - 1)) * powF2 p ε N s * powF p ε N s ∧
      powG p ε N s ^ 2 ≤ (2 + p / (p - 1)) * powF p ε N s ∧
      powG1 p ε N s ^ 2 ≤ (2 + p / (p - 1)) * powF2 p ε N s := by
    generalize 2 + p / (p - 1) = K at hK hK2 ⊢
    by_cases hc : p ≤ 2 ∨ s ≤ N
    · have hw : 0 < s + ε := by linarith
      obtain ⟨h1, h2, h3, h4⟩ := rpow_split hw p
      have ha : 0 < (s + ε) ^ (p - 2) := Real.rpow_pos_of_pos hw _
      have := struct_ineqs_uncapped hp hK hK2 ha h4 hw
      rw [powF1_eq_of_le hε hs hc, powF2, powCap_eq_of_le hs hc, powF_eq_of_le hε hs hc,
        powG_eq_of_le hε hs hc, powG1, powCap_eq_of_le hs hc, h1, h2, h3]
      exact this
    · push Not at hc
      obtain ⟨hp2, hsN⟩ := hc
      have hL : 0 < N + ε := by linarith
      obtain ⟨h1, h2, h3, h4⟩ := rpow_split hL p
      have ha : 0 < (N + ε) ^ (p - 2) := Real.rpow_pos_of_pos hL _
      have := struct_ineqs_capped hp2 hK hK2 ha h4 hL (sub_nonneg.2 hsN.le)
      have hcap' : powCap p ε N s = N + ε := powCap_eq_cap hp2 hsN.le hN
      rw [powF1_eq_of_ge hp2 hε hN hsN.le, powF2, hcap', powF_eq_of_ge hp2 hε hN hsN.le,
        powG_eq_of_ge hp2 hε hN hsN.le, powG1, hcap', h1, h2, h3]
      convert this using 3 <;> ring
  rw [deriv_deriv_powF hε hN, deriv_powF hε hN, deriv_powG hε hN]
  exact ⟨powF_nonneg hp hε hN hs, powF2_nonneg hp hε hN s, key.1, key.2.1, key.2.2,
    powF_le hp hε hN hs, powG_nonneg hp hε hN hs, fun hsN => powG_eq_of_le hε hs (Or.inr hsN)⟩

end

end PDE.Parabolic.LocalMax
