module

public import PDEFoundation.Sobolev.W1p.Composition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A `C¹` cutoff of the power function and lowering the Sobolev exponent

For `γ ≥ 1` and `n ≥ 0`, the function `t ↦ ∫_0^t γ (min (max s 0) n)^(γ-1) ds` is `C¹`, has
derivative bounded by `γ n^(γ-1)`, and agrees with `t ↦ t^γ` on `[0, n]`, with derivative
`γ t^(γ-1)` there.  This is the chain-rule input for Step 2 of the Sobolev--Poincaré inequality on
normalized convex domains.  We also record that a `W^{1,p}` function on a domain of finite volume
is a `W^{1,1}` function.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The `C¹` cutoff of the power function `t ↦ t^γ` at height `n`. -/
noncomputable def powerCutoff (γ n : ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, γ * (min (max s 0) n) ^ (γ - 1)

section Power

variable {γ n : ℝ}

theorem continuous_powerCutoff_deriv_aux (hγ : 1 ≤ γ) :
    Continuous fun s : ℝ => γ * (min (max s 0) n) ^ (γ - 1) :=
  continuous_const.mul ((Real.continuous_rpow_const (by linarith)).comp
    ((continuous_id.max continuous_const).min continuous_const))

theorem hasDerivAt_powerCutoff (hγ : 1 ≤ γ) (t : ℝ) :
    HasDerivAt (powerCutoff γ n) (γ * (min (max t 0) n) ^ (γ - 1)) t :=
  (Continuous.integral_hasStrictDerivAt (continuous_powerCutoff_deriv_aux hγ) 0 t).hasDerivAt

theorem deriv_powerCutoff (hγ : 1 ≤ γ) (t : ℝ) :
    deriv (powerCutoff γ n) t = γ * (min (max t 0) n) ^ (γ - 1) :=
  (hasDerivAt_powerCutoff hγ t).deriv

theorem contDiff_powerCutoff (hγ : 1 ≤ γ) : ContDiff ℝ 1 (powerCutoff γ n) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_powerCutoff hγ t).differentiableAt, ?_⟩
  have : deriv (powerCutoff γ n) = fun s => γ * (min (max s 0) n) ^ (γ - 1) :=
    funext (deriv_powerCutoff hγ)
  rw [this]
  exact continuous_powerCutoff_deriv_aux hγ

theorem abs_deriv_powerCutoff_le (hγ : 1 ≤ γ) (hn : 0 ≤ n) (t : ℝ) :
    |deriv (powerCutoff γ n) t| ≤ γ * n ^ (γ - 1) := by
  rw [deriv_powerCutoff hγ]
  have h0 : 0 ≤ min (max t 0) n := le_min (le_max_right _ _) hn
  have h1 : 0 ≤ γ * (min (max t 0) n) ^ (γ - 1) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg h0 _)
  rw [abs_of_nonneg h1]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow h0 (min_le_right _ _) (by linarith)) (by linarith)

theorem powerCutoff_zero : powerCutoff γ n 0 = 0 := by
  simp [powerCutoff]

theorem deriv_powerCutoff_of_mem (hγ : 1 ≤ γ) {t : ℝ} (ht0 : 0 ≤ t) (htn : t ≤ n) :
    deriv (powerCutoff γ n) t = γ * t ^ (γ - 1) := by
  rw [deriv_powerCutoff hγ, max_eq_left ht0, min_eq_left htn]

theorem powerCutoff_of_mem (hγ : 1 ≤ γ) {t : ℝ} (ht0 : 0 ≤ t) (htn : t ≤ n) :
    powerCutoff γ n t = t ^ γ := by
  have hγ0 : 0 < γ := by linarith
  unfold powerCutoff
  have hcongr : ∫ s in (0 : ℝ)..t, γ * (min (max s 0) n) ^ (γ - 1) =
      ∫ s in (0 : ℝ)..t, γ * s ^ (γ - 1) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht0] at hs
    rw [max_eq_left hs.1, min_eq_left (hs.2.trans htn)]
  rw [hcongr, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < γ - 1))]
  rw [show γ - 1 + 1 = γ by ring, Real.zero_rpow hγ0.ne']
  field_simp
  ring

end Power

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- On a domain of finite volume, a `W^{1,p}` function with `p ≥ 1` is a `W^{1,1}` function. -/
def toOne [IsFiniteMeasure (volumeOn U)] (hp : 1 ≤ p) (u : W1pFunction U p) :
    W1pFunction U 1 where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memLp.mono_exponent hp
  gradMemLp := fun i => (u.gradMemLp i).mono_exponent hp
  hasWeakGradient := u.hasWeakGradient

@[simp]
theorem toOne_toFun [IsFiniteMeasure (volumeOn U)] (hp : 1 ≤ p) (u : W1pFunction U p) :
    (u.toOne hp).toFun = u.toFun := rfl

@[simp]
theorem toOne_grad [IsFiniteMeasure (volumeOn U)] (hp : 1 ≤ p) (u : W1pFunction U p) :
    (u.toOne hp).grad = u.grad := rfl

end W1pFunction

end PDE
