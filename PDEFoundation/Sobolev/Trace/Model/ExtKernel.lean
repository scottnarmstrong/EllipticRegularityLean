module

public import PDEFoundation.Sobolev.Trace.Model.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The mollifier and the cutoff of the model extension operator

Concrete choices of the smooth kernel `extKernel n` (supported in the round unit ball) and the
smooth cutoff `extCutoff` in the normal variable, together with the profiles of the `x'`- and
`t`-derivatives of the dilated kernel `t⁻ⁿ ρ(z / t)` and their cancellation `∫ ψ = 0`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The smooth bump from which the kernel is normalised. -/
noncomputable def extBump (n : ℕ) : ContDiffBump (0 : Vec n) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    nlinarith⟩

/-- Fixed mollifier: smooth, `≥ 0`, supported in `euclideanBall 0 1`, integral `1`. -/
noncomputable def extKernel (n : ℕ) : Vec n → ℝ := (extBump n).normed volume

/-- Fixed cutoff in `t`: smooth, `0 ≤ χ ≤ 1`, `χ = 1` on `t ≤ 1/2`, `χ = 0` on `t ≥ 1`. -/
noncomputable def extCutoff : ℝ → ℝ := fun t => Real.smoothTransition (2 - 2 * t)

theorem extKernel_contDiff (n : ℕ) : ContDiff ℝ 1 (extKernel n) :=
  (extBump n).contDiff_normed

theorem extKernel_nonneg (n : ℕ) (w : Vec n) : 0 ≤ extKernel n w :=
  (extBump n).nonneg_normed w

theorem extKernel_integral (n : ℕ) : ∫ w, extKernel n w = 1 :=
  (extBump n).integral_normed

theorem extKernel_integrable (n : ℕ) : Integrable (extKernel n) :=
  (extBump n).integrable_normed

theorem extKernel_hasCompactSupport (n : ℕ) : HasCompactSupport (extKernel n) :=
  (extBump n).hasCompactSupport_normed

theorem sqrt_natCast_mul_le_one (n : ℕ) {r : ℝ} (hr : r ≤ 1 / ((n : ℝ) + 1)) (hr0 : 0 ≤ r) :
    Real.sqrt n * r ≤ 1 := by
  have h1 : Real.sqrt n ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc Real.sqrt n * r ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
        mul_le_mul h1 hr hr0 h2.le
    _ = 1 := by field_simp

/-- The topological support of the kernel lies in the closed Euclidean unit ball. -/
theorem vecEuclideanNorm_le_one_of_mem_tsupport (n : ℕ) {w : Vec n}
    (hw : w ∈ tsupport (extKernel n)) : vecEuclideanNorm w ≤ 1 := by
  have h : w ∈ Metric.closedBall (0 : Vec n) (1 / ((n : ℝ) + 1)) := by
    have := (extBump n).tsupport_normed_eq (μ := volume)
    rw [extKernel, this] at hw
    exact hw
  have h1 : ‖w‖ ≤ 1 / ((n : ℝ) + 1) := by simpa using h
  exact (vecEuclideanNorm_le_sqrt_natCast_mul_norm w).trans (sqrt_natCast_mul_le_one n h1 (norm_nonneg w))

theorem extKernel_eq_zero_of_one_lt (n : ℕ) {w : Vec n} (hw : 1 < vecEuclideanNorm w) :
    extKernel n w = 0 := by
  by_contra h
  exact absurd (vecEuclideanNorm_le_one_of_mem_tsupport n (subset_tsupport _ h)) (not_le.2 hw)

theorem fderiv_extKernel_eq_zero_of_one_lt (n : ℕ) {w : Vec n} (hw : 1 < vecEuclideanNorm w) :
    fderiv ℝ (extKernel n) w = 0 := by
  by_contra h
  exact absurd (vecEuclideanNorm_le_one_of_mem_tsupport n
    (support_fderiv_subset ℝ (f := extKernel n) h)) (not_le.2 hw)

end PDE.TraceLane
