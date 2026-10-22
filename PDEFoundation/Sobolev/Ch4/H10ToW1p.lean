module

public import PDEFoundation.Sobolev.Ch4.H10Algebra
public import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-!
# `H¹₀(U) ⊆ W^{1,p}₀(U)` for `p ≤ 2` on sets of finite measure

On a set of finite measure, an `H¹(U)` function is a `W^{1,p}(U)` function for `1 ≤ p ≤ 2`, and
the supported smooth approximation of an `H¹₀(U)` function converges also in `L^p`
(Hölder on a finite measure).
-/

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

theorem isFiniteMeasure_volumeOn_of_ne_top (hfin : volume U ≠ ⊤) :
    IsFiniteMeasure (volumeOn U) := ⟨by simpa [volumeOn] using hfin.lt_top⟩

/-- On a set of finite measure, `L²` convergence gives `L^p` convergence for `p ≤ 2`. -/
theorem tendsto_eLpNorm_of_tendsto_two (hfin : volume U ≠ ⊤) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp2 : p ≤ 2) {F : ℕ → Vec d → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (F n) (volumeOn U))
    (h : Tendsto (fun n => eLpNorm (F n) 2 (volumeOn U)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p (volumeOn U)) atTop (𝓝 0) := by
  have := isFiniteMeasure_volumeOn_of_ne_top hfin
  have hc : (volumeOn U) Set.univ ^ (1 / p.toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg ?_ (measure_ne_top _ _)).ne
    have h1 : (1 : ℝ) / (2 : ℝ≥0∞).toReal ≤ 1 / p.toReal := by
      have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne'
        (ne_top_of_le_ne_top (by norm_num) hp2)
      have := ENNReal.toReal_mono (by norm_num) hp2
      exact one_div_le_one_div_of_le hp0 this
    linarith
  have hb := ENNReal.Tendsto.mul_const h (Or.inr hc)
  rw [zero_mul] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => bot_le)
    (fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 (hm n))

/-- An `H¹(U)` function on a set of finite measure, regarded as a `W^{1,p}(U)` function
(`p ≤ 2`) with the same value and gradient representatives. -/
noncomputable def h1ToW1p (hfin : volume U ≠ ⊤) {p : ℝ≥0∞} (hp2 : p ≤ 2) (u : H1Function U) :
    W1pFunction U p :=
  haveI := isFiniteMeasure_volumeOn_of_ne_top hfin
  { toFun := u.toFun
    grad := u.grad
    memLp := u.memL2.mono_exponent hp2
    gradMemLp := fun i => (u.gradMemL2 i).mono_exponent hp2
    hasWeakGradient := u.hasWeakGradient }

/-- An `H¹₀(U)` function on a set of finite measure has a supported smooth approximation in
`W^{1,p}(U)` for `1 ≤ p ≤ 2`: it is a `W^{1,p}₀(U)` function. -/
noncomputable def h10SupportedSmoothApproximationW1p (hfin : volume U ≠ ⊤) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (u : H10Function U) :
    (h1ToW1p hfin hp2 u.toH1Function).SupportedSmoothApproximation where
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_tsupport_subset := u.approx_support_subset
  tendsto_value := by
    refine tendsto_eLpNorm_of_tendsto_two hfin hp hp2 (fun n => ?_) u.tendsto_approx
    exact ((u.approx_smooth n).continuous.aestronglyMeasurable).sub
      u.toH1Function.memL2.aestronglyMeasurable
  tendsto_grad := fun i => by
    refine tendsto_eLpNorm_of_tendsto_two hfin hp hp2 (fun n => ?_) (u.tendsto_approx_grad i)
    exact (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable.sub
      (u.toH1Function.gradMemL2 i).aestronglyMeasurable

end PDE.Ch4Infra
