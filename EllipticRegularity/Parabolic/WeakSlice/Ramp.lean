module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Smooth ramps: an elementary du Bois-Reymond step

If `m` is continuous on `ℝ` and `∫ m θ' = ∫ g θ` for all `C¹` test functions `θ` supported in
`(p, q)`, then `m p - m q = ∫_{(p,q)} g`.  Used for the weak slice lemma.
-/

@[expose] public section

namespace PDE.Parabolic.WeakSlice

open MeasureTheory Set Filter Topology

/-- Derivative of the smooth step. -/
noncomputable def rampDeriv : ℝ → ℝ := deriv Real.smoothTransition

theorem rampDeriv_hasDerivAt (x : ℝ) : HasDerivAt Real.smoothTransition (rampDeriv x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt

theorem rampDeriv_continuous : Continuous rampDeriv := by
  have := (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  exact this

theorem rampDeriv_eq_zero_of_lt {x : ℝ} (hx : x < 0) : rampDeriv x = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [rampDeriv, this.deriv_eq]; simp

theorem rampDeriv_eq_zero_of_gt {x : ℝ} (hx : 1 < x) : rampDeriv x = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [rampDeriv, this.deriv_eq]; simp

theorem rampDeriv_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : rampDeriv x = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact rampDeriv_eq_zero_of_lt h
  · exact rampDeriv_eq_zero_of_gt h

theorem rampDeriv_integrable : Integrable rampDeriv := by
  refine (rampDeriv_continuous.integrableOn_Icc (a := 0) (b := 1)).integrable_of_forall_notMem_eq_zero ?_
  intro x hx; exact rampDeriv_eq_zero_of_notMem hx

theorem integral_rampDeriv : ∫ x, rampDeriv x = 1 := by
  have h1 : ∫ x, rampDeriv x = ∫ x in Icc (0:ℝ) 1, rampDeriv x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx; exact rampDeriv_eq_zero_of_notMem hx
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => rampDeriv_hasDerivAt x)
      (rampDeriv_continuous.intervalIntegrable _ _)]
  simp [Real.smoothTransition.zero_of_nonpos, Real.smoothTransition.one_of_one_le]

/-- Substitution: the mollified evaluation of a continuous function tends to its value. -/
theorem tendsto_ramp_avg (m : ℝ → ℝ) (hm : Continuous m) (b κ : ℝ) :
    Tendsto (fun ε : ℝ => ∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε)))
      (𝓝[>] 0) (𝓝 (m b)) := by
  have hsub : ∀ ε : ℝ, 0 < ε → ∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε))
      = ∫ x, m (b + ε * (κ + x)) * rampDeriv x := by
    intro ε hε
    have h1 : ∫ τ, m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε))
        = ∫ y, m (b + κ * ε + y) * (ε⁻¹ * rampDeriv (y / ε)) := by
      have := integral_add_left_eq_self (μ := volume)
        (f := fun τ => m τ * (ε⁻¹ * rampDeriv ((τ - (b + κ * ε)) / ε))) (b + κ * ε)
      rw [← this]
      congr 1; ext y
      have : b + κ * ε + y - (b + κ * ε) = y := by ring
      simp only [this]
    rw [h1]
    have h2 := Measure.integral_comp_mul_left
      (fun y => m (b + κ * ε + y) * (ε⁻¹ * rampDeriv (y / ε))) ε
    rw [smul_eq_mul, abs_inv, abs_of_pos hε] at h2
    have h3 : ∫ y, m (b + κ * ε + y) * (ε⁻¹ * rampDeriv (y / ε))
        = ε * ∫ x, m (b + κ * ε + ε * x) * (ε⁻¹ * rampDeriv (ε * x / ε)) := by
      rw [h2]; field_simp
    rw [h3, ← integral_const_mul]
    congr 1; ext x
    have : ε * x / ε = x := by field_simp
    rw [this]
    have : b + κ * ε + ε * x = b + ε * (κ + x) := by ring
    rw [this]; field_simp
  refine Tendsto.congr' (f₁ := fun ε : ℝ => ∫ x, m (b + ε * (κ + x)) * rampDeriv x) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε using (hsub ε hε).symm
  have hmb : m b = ∫ x, m b * rampDeriv x := by
    rw [integral_const_mul, integral_rampDeriv, mul_one]
  rw [hmb]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := b - (|κ| + 2)) (b := b + (|κ| + 2))).exists_bound_of_continuousOn
    hm.continuousOn
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (|M| + 0) * ‖rampDeriv x‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    exact (hm.comp (by fun_prop)).aestronglyMeasurable.mul rampDeriv_continuous.aestronglyMeasurable
  · have hε1 : Ioc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioc_mem_nhdsGT zero_lt_one
    filter_upwards [hε1] with ε hε
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · have hmem : b + ε * (κ + x) ∈ Icc (b - (|κ| + 2)) (b + (|κ| + 2)) := by
        obtain ⟨h0, h1⟩ := hx
        have := abs_nonneg κ
        have hk1 := neg_abs_le κ
        have hk2 := le_abs_self κ
        constructor <;> nlinarith [hε.1, hε.2]
      rw [norm_mul]
      have := hM _ hmem
      have : ‖m (b + ε * (κ + x))‖ ≤ |M| + 0 := this.trans (by simp [le_abs_self])
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    · simp [rampDeriv_eq_zero_of_notMem hx]
  · exact (rampDeriv_integrable.norm.const_mul _)
  · refine Eventually.of_forall fun x => ?_
    have hc : Tendsto (fun ε : ℝ => b + ε * (κ + x)) (𝓝[>] 0) (𝓝 b) := by
      have : Tendsto (fun ε : ℝ => b + ε * (κ + x)) (𝓝 0) (𝓝 (b + 0 * (κ + x))) :=
        (by fun_prop : Continuous fun ε : ℝ => b + ε * (κ + x)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact ((hm.tendsto b).comp hc).mul_const _
