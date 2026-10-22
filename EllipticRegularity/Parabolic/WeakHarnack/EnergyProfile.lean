/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyPoint

/-! # Shifted power profiles for `v = u + ε`

For `r < 1`, `r ≠ 0`, `ε > 0`: a `C²` profile `F` with `F(s) = (s+ε)^r / r` for `s ≥ 0` (the
nonlinearity of the energy estimate), and a `C¹` profile `G` with `|G(s)| = (s+ε)^(r/2)` (the
Sobolev function), both with bounded derivatives, and the algebraic relations needed later.
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open Set

theorem deriv_comp_add_const' (f : ℝ → ℝ) (c s : ℝ) :
    deriv (fun x => f (x + c)) s = deriv f (s + c) := deriv_comp_add_const f c s

/-- The `C²` profile `F` with `F(s) = (s+ε)^r / r`, `s ≥ 0`. -/
theorem exists_shifted_F {r ε : ℝ} (hr : r < 1) (hr0 : r ≠ 0) (hε : 0 < ε) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ (∃ C : NNReal, LipschitzWith C F) ∧
      (∃ C : NNReal, ∀ s, |deriv F s| ≤ C) ∧ (∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C) ∧
      (∀ s, 0 ≤ deriv F s) ∧
      ∀ s, 0 ≤ s → F s = (s + ε) ^ r / r ∧ deriv F s = (s + ε) ^ (r - 1) ∧
        deriv (deriv F) s = (r - 1) * (s + ε) ^ (r - 2) := by
  obtain ⟨F0, hc, hmono, ⟨B1, hB1⟩, ⟨B2, hB2⟩, hL, hval⟩ :=
    exists_isC2Profile_power (κ := r⁻¹) (r := r) hε (by rw [inv_mul_cancel₀ hr0]; exact zero_le_one)
      hr.le
  have hκ : r⁻¹ * r = 1 := inv_mul_cancel₀ hr0
  refine ⟨fun x => F0 (x + ε), hc.comp (contDiff_id.add contDiff_const), ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hL
    exact ⟨L, by simpa [Function.comp_def] using hL.comp (show LipschitzWith 1 (fun x : ℝ => x + ε) from
      LipschitzWith.of_dist_le_mul fun x y => by simp [Real.dist_eq])⟩
  · refine ⟨⟨|B1|, abs_nonneg _⟩, fun s => ?_⟩
    rw [deriv_comp_add_const']
    exact (hB1 _).trans (le_abs_self _)
  · refine ⟨⟨|B2|, abs_nonneg _⟩, fun s => ?_⟩
    have : deriv (deriv fun x => F0 (x + ε)) = fun s => deriv (deriv F0) (s + ε) := by
      funext s
      rw [show (deriv fun x => F0 (x + ε)) = fun s => deriv F0 (s + ε) from
        funext fun s => deriv_comp_add_const' F0 ε s, deriv_comp_add_const']
    rw [this]
    exact (hB2 _).trans (le_abs_self _)
  · intro s
    rw [deriv_comp_add_const']
    exact hmono _
  · intro s hs
    have h := hval (s + ε) (by linarith)
    obtain ⟨h0, h1, h2⟩ := h
    have e1 : (deriv fun x => F0 (x + ε)) = fun s => deriv F0 (s + ε) :=
      funext fun s => deriv_comp_add_const' F0 ε s
    refine ⟨?_, ?_, ?_⟩
    · show F0 (s + ε) = _
      rw [h0]; ring
    · rw [e1]; show deriv F0 (s + ε) = _; rw [h1]; simp only [hκ, one_mul]
    · rw [e1, deriv_comp_add_const', h2]; simp only [hκ, one_mul]

/-- The `C¹` profile `G` with `|G(s)| = (s+ε)^(r/2)`, `s ≥ 0`. -/
theorem exists_shifted_G {r ε : ℝ} (hr0 : r ≠ 0) (hε : 0 < ε) (hr : r < 1) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv G s| ≤ M) ∧
      ∀ s, 0 ≤ s → G s ^ 2 = (s + ε) ^ r ∧ deriv G s ^ 2 = (r ^ 2 / 4) * (s + ε) ^ (r - 2) ∧
        |G s| = (s + ε) ^ (r / 2) := by
  have hr2 : r / 2 ≤ 1 := by linarith
  obtain ⟨κ, hκ2, hκr⟩ : ∃ κ : ℝ, κ ^ 2 = 1 ∧ 0 ≤ κ * (r / 2) := by
    rcases lt_or_gt_of_ne hr0 with h | h
    · exact ⟨-1, by norm_num, by nlinarith⟩
    · exact ⟨1, by norm_num, by nlinarith⟩
  obtain ⟨F0, hc, hmono, ⟨B1, hB1⟩, ⟨B2, hB2⟩, hL, hval⟩ :=
    exists_isC2Profile_power (κ := κ) (r := r / 2) hε hκr hr2
  refine ⟨fun x => F0 (x + ε), hc.comp (contDiff_id.add contDiff_const) |>.of_le (by norm_num),
    ⟨|B1|, abs_nonneg _, fun s => ?_⟩, fun s hs => ?_⟩
  · rw [deriv_comp_add_const']
    exact (hB1 _).trans (le_abs_self _)
  · obtain ⟨h0, h1, h2⟩ := hval (s + ε) (by linarith)
    have e1 : deriv (fun x => F0 (x + ε)) s = κ * (r / 2) * (s + ε) ^ (r / 2 - 1) := by
      rw [deriv_comp_add_const', h1]
    have hv : 0 < s + ε := by linarith
    have hsq : ((s + ε) ^ (r / 2)) ^ 2 = (s + ε) ^ r := rpow_half_sq hv r
    have hsq2 : ((s + ε) ^ (r / 2 - 1)) ^ 2 = (s + ε) ^ (r - 2) := by
      have := rpow_half_sq hv (r - 2)
      rwa [show (r - 2) / 2 = r / 2 - 1 by ring] at this
    have hG : (fun x => F0 (x + ε)) s = κ * (s + ε) ^ (r / 2) := h0
    refine ⟨?_, ?_, ?_⟩
    · show F0 (s + ε) ^ 2 = _
      rw [show F0 (s + ε) = κ * (s + ε) ^ (r / 2) from hG, mul_pow, hκ2, one_mul, hsq]
    · rw [e1, mul_pow, mul_pow, hκ2, hsq2]; ring
    · show |F0 (s + ε)| = _
      rw [show F0 (s + ε) = κ * (s + ε) ^ (r / 2) from hG, abs_mul]
      have : |κ| = 1 := by
        have := abs_mul_abs_self κ
        nlinarith [abs_nonneg κ, sq_abs κ]
      rw [this, one_mul, abs_of_pos (Real.rpow_pos_of_pos hv _)]

end PDE.Parabolic.WeakHarnack
