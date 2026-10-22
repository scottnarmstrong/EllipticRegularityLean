module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Sturm
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Friedland--Hayman: the Gaussian weight, admissible parameters and test functions

`gaussW s = exp (-s²/2)` is the unnormalized Gaussian weight.  A parameter `c` is *admissible* at `τ`
if `c ≥ 0` and the initial value problem solution `ouSol c τ` is positive on `(τ, ∞)`.  `GaussTest`
collects the regularity and integrability required of test functions in Barta's inequality.
-/

@[expose] public section

open Set MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- Unnormalized Gaussian weight. -/
def gaussW (s : ℝ) : ℝ := Real.exp (-(s ^ 2) / 2)

/-- `c` is admissible at `τ`: `c ≥ 0` and the IVP solution is positive on `(τ, ∞)`. -/
def OUAdmissible (τ c : ℝ) : Prop := 0 ≤ c ∧ ∀ s, τ < s → 0 < ouSol c τ s

/-- Admissible test functions on `(τ, ∞)`. -/
structure GaussTest (τ : ℝ) (g g' : ℝ → ℝ) : Prop where
  cont : Continuous g
  eq_zero : ∀ s, s ≤ τ → g s = 0
  hasDeriv : ∀ s, τ < s → HasDerivAt g (g' s) s
  cont' : ContinuousOn g' (Set.Ioi τ)
  int_sq : Integrable fun s => g s ^ 2 * gaussW s
  int_dsq : IntegrableOn (fun s => g' s ^ 2 * gaussW s) (Set.Ioi τ)

theorem gaussW_pos (s : ℝ) : 0 < gaussW s := Real.exp_pos _

theorem gaussW_le_one (s : ℝ) : gaussW s ≤ 1 := by
  unfold gaussW
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg s]

theorem continuous_gaussW : Continuous gaussW := by
  unfold gaussW
  fun_prop

theorem hasDerivAt_gaussW (s : ℝ) : HasDerivAt gaussW (-s * gaussW s) s := by
  have h : HasDerivAt (fun s : ℝ => -(s ^ 2) / 2) (-s) s := by
    have := ((hasDerivAt_pow 2 s).neg).div_const 2
    convert this using 1
    simp
    ring
  have := h.exp
  have e2 : gaussW = fun x => Real.exp (-(x ^ 2) / 2) := rfl
  rw [e2]
  convert this using 1
  ring

/-- `gaussW` is dominated by `exp (-s²/4)`. -/
theorem gaussW_le_exp_quarter (s : ℝ) : gaussW s ≤ Real.exp (-(1 / 4) * s ^ 2) := by
  unfold gaussW
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg s]

/-- Quadratic moment bound: `s² w(s) ≤ 4 exp (-s²/4)`. -/
theorem sq_mul_gaussW_le (s : ℝ) : s ^ 2 * gaussW s ≤ 4 * Real.exp (-(1 / 4) * s ^ 2) := by
  have h1 : s ^ 2 / 4 ≤ Real.exp (s ^ 2 / 4) := by
    have := Real.add_one_le_exp (s ^ 2 / 4)
    linarith
  have h2 : gaussW s = Real.exp (-(1 / 4) * s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by
    unfold gaussW
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2) = 1 := by
    rw [← Real.exp_add]
    rw [show s ^ 2 / 4 + -(1 / 4) * s ^ 2 = 0 by ring, Real.exp_zero]
  have h4 : 0 < Real.exp (-(1 / 4) * s ^ 2) := Real.exp_pos _
  calc s ^ 2 * gaussW s = (s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by
        rw [h2]; ring
    _ ≤ (4 * Real.exp (s ^ 2 / 4)) * Real.exp (-(1 / 4) * s ^ 2) * Real.exp (-(1 / 4) * s ^ 2) := by
        gcongr; linarith
    _ = 4 * Real.exp (-(1 / 4) * s ^ 2) := by
        calc _ = 4 * (Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2))
              * Real.exp (-(1 / 4) * s ^ 2) := by ring
          _ = _ := by rw [h3]; ring

theorem integrable_exp_quarter : Integrable fun s : ℝ => Real.exp (-(1 / 4) * s ^ 2) :=
  integrable_exp_neg_mul_sq (by norm_num)

theorem integrable_gaussW : Integrable gaussW :=
  integrable_exp_quarter.mono' continuous_gaussW.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (gaussW_pos s)]
      exact gaussW_le_exp_quarter s)

theorem integrable_sq_mul_gaussW : Integrable fun s : ℝ => s ^ 2 * gaussW s :=
  (integrable_exp_quarter.const_mul 4).mono'
    (by exact (continuous_pow 2 |>.mul continuous_gaussW).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg s) (gaussW_pos s).le)]
      exact sq_mul_gaussW_le s)

end

end PDE.FHLane
