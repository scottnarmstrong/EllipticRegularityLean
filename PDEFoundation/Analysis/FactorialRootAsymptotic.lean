module

public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Root asymptotics for factorials
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE

/-- The logarithmic form of the factorial root asymptotic. -/
theorem tendsto_log_factorial_div_sub_log :
    Tendsto (fun n : ℕ =>
      Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ))
      atTop (𝓝 (-1)) := by
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  have hlogSeq : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
      atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.log hsqrt.ne'
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hseqZero : Tendsto (fun n : ℕ =>
      Real.log (Stirling.stirlingSeq n) / (n : ℝ)) atTop (𝓝 0) :=
    hlogSeq.div_atTop hcast
  have hlogZeroReal : Tendsto (fun x : ℝ => Real.log x / x)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have htwoCast : Tendsto (fun n : ℕ => (2 : ℝ) * n) atTop atTop :=
    hcast.const_mul_atTop (by norm_num)
  have htwoZero : Tendsto (fun n : ℕ =>
      Real.log ((2 : ℝ) * n) / ((2 : ℝ) * n)) atTop (𝓝 0) :=
    hlogZeroReal.comp htwoCast
  have hsum := hseqZero.add htwoZero
  have htarget : Tendsto (fun n : ℕ =>
      -1 + (Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        Real.log ((2 : ℝ) * n) / ((2 : ℝ) * n))) atTop (𝓝 (-1)) := by
    simpa using (tendsto_const_nhds.add hsum)
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : (2 : ℝ) * n ≠ 0 := mul_ne_zero (by norm_num) hn0
  have hlogdiv : Real.log ((n : ℝ) / Real.exp 1) =
      Real.log (n : ℝ) - 1 := by
    rw [Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp]
  have hformula := Stirling.log_stirlingSeq_formula n
  rw [hlogdiv] at hformula
  field_simp [hn0, htwo]
  simp only [mul_comm (n : ℝ) 2]
  linear_combination 2 * hformula

/-- The `n`th root of `n!`, divided by `n`, tends to `e⁻¹`. -/
theorem tendsto_factorial_rpow_inv_div :
    Tendsto (fun n : ℕ =>
      Real.rpow (n.factorial : ℝ) (1 / (n : ℝ)) / (n : ℝ))
      atTop (𝓝 (Real.exp (-1))) := by
  have hlog := tendsto_log_factorial_div_sub_log
  have hexp : Tendsto (fun n : ℕ => Real.exp
      (Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ)))
      atTop (𝓝 (Real.exp (-1))) :=
    (Real.continuous_exp.tendsto _).comp hlog
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [show Real.rpow (n.factorial : ℝ) (1 / (n : ℝ)) =
      Real.exp (Real.log (n.factorial : ℝ) * (1 / (n : ℝ))) by
    exact Real.rpow_def_of_pos hfacpos _]
  rw [Real.exp_sub, Real.exp_log hnpos]
  congr 2
  ring

end PDE
