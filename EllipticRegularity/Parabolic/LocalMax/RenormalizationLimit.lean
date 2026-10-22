/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.RenormalizationClampF

/-! # The clamp converges to the identity as `M → ∞` -/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open Filter Topology

/-- The clamp parameter sequence `M = n + 1`. -/
theorem tendsto_succ_real : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem tendsto_div_succ (s : ℝ) : Tendsto (fun n : ℕ => s / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_succ_real

theorem tendsto_psiM_succ (s : ℝ) :
    Tendsto (fun n : ℕ => psiM ((n : ℝ) + 1) s) atTop (𝓝 s) := by
  by_cases hs : s = 0
  · subst hs
    simp [psiM]
  · have hslope := hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_arctan 0)
    have hnhds : Tendsto (fun n : ℕ => s / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_div_succ s, Eventually.of_forall fun n => ?_⟩
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero hs this.ne'
    have h2 := (hslope.comp hnhds).const_mul s
    have hlim : (1 : ℝ) / (1 + 0 ^ 2) = 1 := by norm_num
    rw [hlim, mul_one] at h2
    refine h2.congr fun n => ?_
    have hM : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [Function.comp_apply, zero_add, smul_eq_mul, Real.arctan_zero, sub_zero, psiM]
    field_simp

theorem tendsto_dpsiM_succ (s : ℝ) :
    Tendsto (fun n : ℕ => dpsiM ((n : ℝ) + 1) s) atTop (𝓝 1) := by
  have h := ((((tendsto_div_succ s).pow 2).const_add 1).inv₀ (by norm_num))
  simp only [dpsiM, one_div]
  simpa using h

theorem tendsto_ddpsiM_succ (s : ℝ) :
    Tendsto (fun n : ℕ => ddpsiM ((n : ℝ) + 1) s) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 2 * (s / ((n : ℝ) + 1)) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    by simpa using (((tendsto_div_succ s).const_mul 2).div_atTop tendsto_succ_real)
  have h2 := ((((tendsto_div_succ s).pow 2).const_add 1).pow 2)
  have h3 := (h1.neg).div h2 (by norm_num)
  simpa [ddpsiM, Pi.div_def] using h3

variable {F : ℝ → ℝ}

theorem tendsto_clampF_succ (hF : ContDiff ℝ 2 F) (v : ℝ) :
    Tendsto (fun n : ℕ => clampF F ((n : ℝ) + 1) v) atTop (𝓝 (F v)) :=
  ((hF.continuous.tendsto v).comp (tendsto_psiM_succ v))

theorem tendsto_deriv_clampF_succ (hF : ContDiff ℝ 2 F) (v : ℝ) :
    Tendsto (fun n : ℕ => deriv (clampF F ((n : ℝ) + 1)) v) atTop (𝓝 (deriv F v)) := by
  have hc : Continuous (deriv F) := (Chain.contDiff_deriv_of_two hF).continuous
  have h := ((hc.tendsto v).comp (tendsto_psiM_succ v)).mul (tendsto_dpsiM_succ v)
  rw [mul_one] at h
  refine h.congr fun n => ?_
  have hM : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp [deriv_clampF hF hM]

theorem tendsto_deriv_deriv_clampF_succ (hF : ContDiff ℝ 2 F) (v : ℝ) :
    Tendsto (fun n : ℕ => deriv (deriv (clampF F ((n : ℝ) + 1))) v) atTop
      (𝓝 (deriv (deriv F) v)) := by
  have hc1 : Continuous (deriv F) := (Chain.contDiff_deriv_of_two hF).continuous
  have hc2 : Continuous (deriv (deriv F)) :=
    (contDiff_one_iff_deriv.mp (Chain.contDiff_deriv_of_two hF)).2
  have hp := tendsto_psiM_succ v
  have h := ((((hc2.tendsto v).comp hp).mul (tendsto_dpsiM_succ v)).mul
    (tendsto_dpsiM_succ v)).add (((hc1.tendsto v).comp hp).mul (tendsto_ddpsiM_succ v))
  simp only [mul_one, mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  have hM : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp [deriv_deriv_clampF hF hM]

end PDE.Parabolic.LocalMax
