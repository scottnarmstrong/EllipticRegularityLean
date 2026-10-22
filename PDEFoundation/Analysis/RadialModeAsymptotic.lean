module

public import PDEFoundation.Analysis.RadialModeParameter
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace PDE
open Filter
open scoped Topology

/-- The exact oscillation parameter has the manuscript's asymptotic `2/p`. -/
theorem tendsto_mul_radialMode_critical_parameter :
    Tendsto (fun p : ℝ => p * (2 * (p - 1) / (p ^ 2 - 2 * p + 2)))
      atTop (𝓝 2) := by
  let f : ℝ → ℝ := fun t => 2 * (1 - t) / (1 - 2 * t + 2 * t ^ 2)
  have hc : ContinuousAt f 0 := by
    dsimp only [f]
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have hlim : Tendsto (fun p : ℝ => f p⁻¹) atTop (𝓝 2) := by
    have hf0 : f 0 = 2 := by norm_num [f]
    rw [← hf0]
    exact hc.tendsto.comp tendsto_inv_atTop_zero
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with p hp
  dsimp only [f]
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hd : p ^ 2 - 2 * p + 2 ≠ 0 := by
    nlinarith only [sq_nonneg (p - 1)]
  have hn : 1 - 2 * p⁻¹ + 2 * (p⁻¹) ^ 2 ≠ 0 := by
    nlinarith only [sq_nonneg (p⁻¹ - (1 / 2 : ℝ))]
  field_simp [hp0, hd, hn]

end PDE
