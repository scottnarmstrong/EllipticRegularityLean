/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.MeasureLimit

/-! # Strong `L²` convergence under Lipschitz compositions -/

@[expose] public section

namespace PDE.Parabolic.Chain

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- A Lipschitz scalar composition preserves `L²` on a finite measure space. -/
theorem memLp_comp_lipschitz {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {F : ℝ → ℝ} (hF : ∃ C : NNReal, LipschitzWith C F)
    {f : X → ℝ} (hf : MemLp f 2 μ) : MemLp (fun x => F (f x)) 2 μ := by
  obtain ⟨C, hC⟩ := hF
  have hcomp : AEStronglyMeasurable (fun x => F (f x)) μ := by
    exact (hC.continuous.measurable.aestronglyMeasurable).comp_aemeasurable
      hf.aestronglyMeasurable.aemeasurable
  have hdiff : AEStronglyMeasurable (fun x => F (f x) - F 0) μ :=
    hcomp.sub (aestronglyMeasurable_const)
  have hbound : ∀ᵐ x ∂μ, ‖F (f x) - F 0‖ ≤ (C : ℝ) * ‖f x‖ := by
    filter_upwards with x
    have h := hC.dist_le_mul (f x) 0
    simpa [dist_eq_norm] using h
  have hdiffLp : MemLp (fun x => F (f x) - F 0) 2 μ :=
    hf.of_le_mul hdiff hbound
  have hconst : MemLp (fun _ : X => F 0) 2 μ := memLp_const (F 0)
  have hsum := hdiffLp.add hconst
  have heq : (fun x => F (f x)) =
      (fun x => F (f x) - F 0) + (fun _ : X => F 0) := by
    funext x
    simp
  rw [heq]
  exact hsum

/-- Lipschitz composition carries strong `L²` convergence to strong `L²`
convergence. -/
theorem tendsto_eLpNorm_comp_sub_of_lipschitz {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {F : ℝ → ℝ}
    (hF : ∃ C : NNReal, LipschitzWith C F) {f : ℕ → X → ℝ} {f₀ : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (hfl : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((fun x => F (f n x)) - (fun x => F (f₀ x))) 2 μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hF
  have hcompLp : ∀ n, MemLp (fun x => F (f n x)) 2 μ :=
    fun n => memLp_comp_lipschitz ⟨C, hC⟩ (hf n)
  have hcompLp₀ := memLp_comp_lipschitz ⟨C, hC⟩ hf₀
  have hbound (n : ℕ) :
      ∀ᵐ x ∂μ,
        ‖F (f n x) - F (f₀ x)‖ ≤ (C : ℝ) * ‖f n x - f₀ x‖ := by
    filter_upwards with x
    have h := hC.dist_le_mul (f n x) (f₀ x)
    simpa [dist_eq_norm] using h
  have hnorm (n : ℕ) := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((hcompLp n).sub hcompLp₀).aestronglyMeasurable (hbound n) (2 : ℝ≥0∞)
  have hconst : Tendsto
      (fun n => ENNReal.ofReal (C : ℝ) * eLpNorm (f n - f₀) 2 μ) atTop
      (𝓝 (ENNReal.ofReal (C : ℝ) * 0)) :=
    ENNReal.Tendsto.const_mul hfl (Or.inr ENNReal.ofReal_ne_top)
  have hupper : Tendsto
      (fun n => ENNReal.ofReal (C : ℝ) * eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0) := by
    simpa using hconst
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => by positivity) ?_
  exact Eventually.of_forall fun n => hnorm n

/-- Continuous compositions preserve convergence in measure on a finite measure
space. This form is useful for bounded nonlinear coefficients such as `F''`;
no global Lipschitz estimate on the coefficient is needed. -/
theorem tendstoInMeasure_comp_continuous {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {F : ℝ → ℝ} (hF : Continuous F)
    {f : ℕ → X → ℝ} {f₀ : X → ℝ}
    (hf : TendstoInMeasure μ f atTop f₀)
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) :
    TendstoInMeasure μ (fun n x => F (f n x)) atTop (fun x => F (f₀ x)) := by
  have hcompMeas : ∀ n, AEStronglyMeasurable (fun x => F (f n x)) μ := fun n =>
    hF.measurable.aestronglyMeasurable.comp_aemeasurable (hfm n).aemeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hcompMeas).2
  intro ns hns
  obtain ⟨ms, hms, hfae⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hfae] with x hx
  exact hF.continuousAt.tendsto.comp hx

end PDE.Parabolic.Chain
