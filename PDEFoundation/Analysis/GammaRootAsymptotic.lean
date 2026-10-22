module

public import PDEFoundation.Analysis.GammaLogAsymptotic

/-!
# Root asymptotics of the real Gamma function
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE

/-- The real Gamma root has the Stirling asymptotic `Γ(p+1)^(1/p) ∼ p/e`. -/
theorem tendsto_Gamma_add_one_rpow_inv_div :
    Tendsto (fun p : ℝ =>
      Real.rpow (Real.Gamma (p + 1)) (1 / p) / p)
      atTop (𝓝 (Real.exp (-1))) := by
  have hexp : Tendsto (fun p : ℝ => Real.exp
      (Real.log (Real.Gamma (p + 1)) / p - Real.log p))
      atTop (𝓝 (Real.exp (-1))) :=
    (Real.continuous_exp.tendsto _).comp
      tendsto_log_Gamma_add_one_div_sub_log
  apply hexp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
  have hGamma : 0 < Real.Gamma (p + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  rw [show Real.rpow (Real.Gamma (p + 1)) (1 / p) =
      Real.exp (Real.log (Real.Gamma (p + 1)) * (1 / p)) by
    exact Real.rpow_def_of_pos hGamma _]
  rw [Real.exp_sub, Real.exp_log hp]
  congr 2
  ring

/-- The normalized lower-bound expression in the forcing example has its
literal asymptotic constant. -/
theorem tendsto_half_Gamma_add_one_rpow_inv_sub_one_div :
    Tendsto (fun p : ℝ =>
      ((1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1) / p)
      atTop (𝓝 ((1 / 2 : ℝ) * Real.exp (-1))) := by
  have hroot := tendsto_Gamma_add_one_rpow_inv_div
  have hinv : Tendsto (fun p : ℝ => 1 / p) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hhalf : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hlim : Tendsto (fun p : ℝ =>
      (1 / 2 : ℝ) * (Real.rpow (Real.Gamma (p + 1)) (1 / p) / p) - 1 / p)
      atTop (𝓝 ((1 / 2 : ℝ) * Real.exp (-1))) := by
    simpa only [sub_zero] using (hhalf.mul hroot).sub hinv
  apply hlim.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with p hp
  field_simp

end PDE
