module

public import EllipticRegularity.DeGiorgi.Assembly.Statements
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Hölder exponent in Theorem 4.21
-/

@[expose] public section

namespace PDE.DGNMAssembly

theorem alpha_facts {H : ℝ} (hH : 3 ≤ H) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 / H ≤ α ∧ (1 / 2 : ℝ) ^ α = (H - 1) / (H + 1) := by
  have hH1 : 0 < H - 1 := by linarith
  have hH2 : 0 < H + 1 := by linarith
  set q : ℝ := (H + 1) / (H - 1) with hq
  have hq1 : 1 < q := by rw [hq, lt_div_iff₀ hH1]; linarith
  have hq0 : 0 < q := by linarith
  have hq2 : q ≤ 2 := by rw [hq, div_le_iff₀ hH1]; linarith
  refine ⟨Real.logb 2 q, Real.logb_pos (by norm_num) hq1, ?_, ?_, ?_⟩
  · calc Real.logb 2 q ≤ Real.logb 2 2 := Real.logb_le_logb_of_le (by norm_num) hq0 hq2
      _ = 1 := Real.logb_self_eq_one (by norm_num)
  · have hlog : 1 - q⁻¹ ≤ Real.log q := Real.one_sub_inv_le_log_of_pos hq0
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hqinv : 1 - q⁻¹ = 2 / (H + 1) := by
      rw [hq, inv_div]; field_simp; ring
    rw [Real.logb, le_div_iff₀ hl2pos]
    have h2 : 1 / H ≤ 2 / (H + 1) := by
      rw [div_le_div_iff₀ (by linarith) hH2]; linarith
    have h3 : 2 / (H + 1) ≤ 2 / (H + 1) / Real.log 2 * Real.log 2 := by
      rw [div_mul_cancel₀ _ hl2pos.ne']
    nlinarith [hqinv, hlog, h2, h3, mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ 1 / H)]
  · rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.rpow_logb (by norm_num) (by norm_num) hq0, hq, one_div, inv_div]

end PDE.DGNMAssembly
