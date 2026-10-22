module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Essential supremum and infimum from `L^q` bounds

If `‖f‖_{L^{q_N}(μ)} ≤ B` along exponents `q_N → ∞` on a finite measure space, then
`ess sup f ≤ B`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PDE.DGNMMoser

variable {α : Type*} [MeasurableSpace α]

/-- `m ^ (1/q_N) → 1` for a finite nonzero `m` when `q_N → ∞`. -/
theorem tendsto_rpow_inv_one {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmt : m ≠ ⊤) {q : ℕ → ℝ}
    (hq : Tendsto q atTop atTop) :
    Tendsto (fun N => m ^ (1 / q N)) atTop (𝓝 1) := by
  have hr : 0 < m.toReal := ENNReal.toReal_pos hm0 hmt
  have hx : Tendsto (fun N => 1 / q N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hq
  have hxpos : ∀ᶠ N in atTop, 0 < q N := hq.eventually_gt_atTop 0
  have h1 : Tendsto (fun N => m.toReal ^ (1 / q N)) atTop (𝓝 1) := by
    have := (Real.continuousAt_const_rpow hr.ne').tendsto.comp hx
    simpa only [Function.comp_def, Real.rpow_zero] using this
  have h2 := ENNReal.tendsto_ofReal h1
  simp only [ENNReal.ofReal_one] at h2
  refine h2.congr' ?_
  filter_upwards [hxpos] with N hN
  rw [← ENNReal.ofReal_rpow_of_pos hr, ENNReal.ofReal_toReal hmt]

/-- The essential supremum is bounded by any common bound on `L^{q_N}` norms with
`q_N → ∞`, on a finite measure space. -/
theorem essSup_ofReal_le_of_eLpNorm_le {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) {q : ℕ → ℝ} (hq : Tendsto q atTop atTop) {B : ℝ≥0∞}
    (hB : ∀ N, eLpNorm f (ENNReal.ofReal (q N)) μ ≤ B) :
    essSup (fun x => ENNReal.ofReal (f x)) μ ≤ B := by
  by_contra h
  push Not at h
  obtain ⟨t, hBt, htE⟩ := exists_between h
  have htop : t ≠ ⊤ := htE.ne_top
  have hm : μ {x | t < ENNReal.ofReal (f x)} ≠ 0 := by
    intro h0
    have hae : (fun x => ENNReal.ofReal (f x)) ≤ᵐ[μ] fun _ => t := by
      rw [Filter.EventuallyLE, ae_iff]
      simpa using h0
    exact absurd (essSup_le_of_ae_le t hae) (not_le.2 htE)
  set m := μ {x | t < ENNReal.ofReal (f x)} with hmdef
  have hmt : m ≠ ⊤ := measure_ne_top _ _
  have lower : ∀ N, 0 < q N → t * m ^ (1 / q N) ≤ eLpNorm f (ENNReal.ofReal (q N)) μ := by
    intro N hN
    have hne0 : ENNReal.ofReal (q N) ≠ 0 := by simpa using hN
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hN.le]
    have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ q N) μ := hf.enorm.pow_const _
    have hmark := mul_meas_ge_le_lintegral₀ hmeas (t ^ q N)
    have hsub : m ≤ μ {x | t ^ q N ≤ ‖f x‖ₑ ^ q N} := by
      refine measure_mono fun x hx => ?_
      have hx' : t < ENNReal.ofReal (f x) := hx
      have : t < ‖f x‖ₑ := hx'.trans_le (by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _))
      exact (ENNReal.rpow_lt_rpow this hN).le
    have h1 : t ^ q N * m ≤ ∫⁻ x, ‖f x‖ₑ ^ q N ∂μ :=
      (mul_le_mul' le_rfl hsub).trans hmark
    have h2 := ENNReal.rpow_le_rpow h1 (by positivity : (0 : ℝ) ≤ 1 / q N)
    refine le_trans (le_of_eq ?_) h2
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
      mul_one_div_cancel hN.ne', ENNReal.rpow_one]
  have hlim : Tendsto (fun N => t * m ^ (1 / q N)) atTop (𝓝 (t * 1)) :=
    ENNReal.Tendsto.const_mul (tendsto_rpow_inv_one hm hmt hq) (Or.inr htop)
  rw [mul_one] at hlim
  have hev : ∀ᶠ N in atTop, t * m ^ (1 / q N) ≤ B := by
    filter_upwards [hq.eventually_gt_atTop 0] with N hN
    exact (lower N hN).trans (hB N)
  have := le_of_tendsto hlim hev
  exact absurd hBt (not_lt.2 this)

end PDE.DGNMMoser
