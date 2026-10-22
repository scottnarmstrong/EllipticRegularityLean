module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Vanishing `L²` mass on shrinking Euclidean balls -/

@[expose] public section

namespace PDE

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

private instance instNontrivialVecShrinkingBall (d : ℕ) [NeZero d] : Nontrivial (Vec d) :=
  inferInstance

/-- Restricting an actual `L²` field to round balls whose radii tend to zero
makes its `L²` seminorm tend to zero. -/
theorem tendsto_eLpNorm_indicator_euclideanBall_zero
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    {E : Type*} [NormedAddCommGroup E]
    {f : Vec d → E} (hf : MemLp f 2 (volume.restrict U))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm
        ((euclideanBall (0 : Vec d) (2 * ε n)).indicator f)
        2 (volume.restrict U))
      atTop (𝓝 0) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let μ : Measure (Vec d) := volume.restrict U
  let B : ℕ → Set (Vec d) := fun n => euclideanBall 0 (2 * ε n)
  let g : ℕ → Vec d → ℝ := fun n => (B n).indicator (fun x => ‖f x‖)
  have hBmeas (n : ℕ) : MeasurableSet (B n) :=
    measurableSet_euclideanBall 0 (2 * ε n)
  have hgmem (n : ℕ) : MemLp (g n) 2 μ := by
    exact hf.norm.indicator (hBmeas n)
  have hdomInt : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    hf.norm.integrable_sq
  have hne : ∀ᵐ x ∂μ, x ≠ (0 : Vec d) := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! (measure_singleton (μ := μ) (0 : Vec d))
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => (g n x) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hne] with x hx
    have hxnorm : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx
    have hscaled : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hε0
    have hev : ∀ᶠ n in atTop, 2 * ε n < vecEuclideanNorm x :=
      (tendsto_order.1 hscaled).2 _ hxnorm
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hev] with n hn
    have hnot : x ∉ B n := by
      change x ∉ euclideanBall 0 (2 * ε n)
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt
        (mul_pos (by norm_num) (hε n))]
      exact not_lt.mpr (by simpa using hn.le)
    simp [g, hnot]
  have hsq : Tendsto (fun n => ∫ x, (g n x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun x => ‖f x‖ ^ 2)
      (fun n => (hgmem n).integrable_sq.aestronglyMeasurable)
      hdomInt
      (fun n => by
        filter_upwards with x
        by_cases hx : x ∈ B n
        · simp [g, hx]
        · simp [g, hx])
      hpoint
    simpa using h
  have hgzero : Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_zero_of_tendsto_integral_sq hgmem hsq
  have heq (n : ℕ) :
      eLpNorm ((B n).indicator f) 2 μ = eLpNorm (g n) 2 μ := by
    rw [← eLpNorm_norm _ (hf.aestronglyMeasurable.indicator (hBmeas n))]
    apply eLpNorm_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ B n
    · simp [g, hx]
    · simp [g, hx]
  simpa only [μ, B, heq] using hgzero

/-- Real-valued form of the shrinking-ball `L²` seminorm convergence. -/
theorem tendsto_toReal_eLpNorm_indicator_euclideanBall_zero
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    {E : Type*} [NormedAddCommGroup E]
    {f : Vec d → E} (hf : MemLp f 2 (volume.restrict U))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun n => (eLpNorm
        ((euclideanBall (0 : Vec d) (2 * ε n)).indicator f)
        2 (volume.restrict U)).toReal)
      atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_eLpNorm_indicator_euclideanBall_zero hd hf ε hε hε0)

end

end PDE
