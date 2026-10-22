module

public import PDEFoundation.Analysis.GammaRootAsymptotic
public import Mathlib.Topology.Order.OrderClosed

/-! # The logarithmic lower bound excludes sublinear forcing constants -/

@[expose] public section

namespace PDE
open Filter
open scoped Topology

/-- The literal Gamma lower bound eventually defeats any fixed additive
constant and any forcing coefficient whose ratio to the exponent tends to zero.
The sharpness witness supplies this lower bound in the PDE application. -/
theorem not_forall_half_Gamma_le_constant_add_sublinear
    (A : ℝ) (b : ℝ → ℝ)
    (hb : Tendsto (fun p : ℝ => b p / p) atTop (𝓝 0)) :
    ¬∀ p : ℝ, 2 ≤ p →
      (1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1 ≤ A + 2 * b p := by
  have hA : Tendsto (fun p : ℝ => A / p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hb2 : Tendsto (fun p : ℝ => 2 * b p / p) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).mul hb
    simpa only [mul_zero, mul_div_assoc] using h
  have hsum : Tendsto (fun p : ℝ => (A + 2 * b p) / p) atTop (𝓝 0) := by
    simpa only [zero_add, add_div] using hA.add hb2
  intro hbound
  have hle : (1 / 2 : ℝ) * Real.exp (-1) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_half_Gamma_add_one_rpow_inv_sub_one_div hsum (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
      exact div_le_div_of_nonneg_right (hbound p hp)
        (le_trans (by norm_num : (0 : ℝ) ≤ 2) hp))
  exact (not_le_of_gt (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.exp_pos (-1)))) hle

end PDE
