module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Clamps

/-!
# Bounded higher-integrability clips of `H¹` representatives

This module regards the existing symmetric `W^{1,2}` clamp as a
`W^{1,p}` representative when the original chosen gradient already has
coordinatewise `L^p` control. The value representative is bounded, and the
chosen weak gradient is preserved on the unclipped region.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Symmetric clipping of an `H¹` representative, regarded as a
representative-level `W^{1,p}` function using higher integrability of its
chosen weak gradient. -/
noncomputable def higherIntegrabilityClamp
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (_hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) :
    W1pFunction U (ENNReal.ofReal p) := by
  letI : IsFiniteMeasure (volumeOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_volumeOn
  let clip := u.toW1pFunction.clampConst hU (by norm_num) (by norm_num) (-k) k
  refine
    { toFun := clip.toFun
      grad := clip.grad
      memLp := ?_
      gradMemLp := ?_
      hasWeakGradient := clip.hasWeakGradient }
  · refine MemLp.of_bound clip.memLp.aestronglyMeasurable k ?_
    filter_upwards with x
    rw [show clip.toFun x = min (max (u.toFun x) (-k)) k by
      simp only [clip, W1pFunction.clampConst_toFun,
        H1Function.toW1pFunction_toFun]]
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_min (le_max_right _ _) (neg_le_self hk)
    · exact min_le_right _ _
  · intro i
    refine MemLp.of_le (hgrad i) (clip.gradMemLp i).aestronglyMeasurable ?_
    filter_upwards with x
    rw [show clip.grad x =
        {y | -k < u.toFun y ∧ u.toFun y < k}.indicator u.grad x by
      simp only [clip, W1pFunction.clampConst_grad,
        H1Function.toW1pFunction_toFun, H1Function.toW1pFunction_grad]]
    by_cases hx : x ∈ {y | -k < u.toFun y ∧ u.toFun y < k}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Pi.zero_apply, norm_zero]
      exact norm_nonneg _

@[simp]
theorem higherIntegrabilityClamp_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) :
    (u.higherIntegrabilityClamp hU p hp hgrad k hk).toFun =
      fun x => max (-k) (min (u.toFun x) k) := by
  funext x
  rw [show (u.higherIntegrabilityClamp hU p hp hgrad k hk).toFun x =
      min (max (u.toFun x) (-k)) k by
    simp only [higherIntegrabilityClamp, W1pFunction.clampConst_toFun,
      H1Function.toW1pFunction_toFun]]
  rw [min_max_distrib_right, min_eq_left (neg_le_self hk), max_comm]

@[simp]
theorem higherIntegrabilityClamp_grad
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) :
    (u.higherIntegrabilityClamp hU p hp hgrad k hk).grad =
      fun x => {y | -k < u.toFun y ∧ u.toFun y < k}.indicator u.grad x := by
  simp only [higherIntegrabilityClamp, W1pFunction.clampConst_grad,
    H1Function.toW1pFunction_toFun, H1Function.toW1pFunction_grad]

/-- Symmetric higher-integrability clipping contracts every coordinate of the
chosen weak gradient with constant one. -/
theorem eLpNormOn_higherIntegrabilityClamp_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (p : ℝ) (hp : 2 ≤ p) (u : H1Function U)
    (hgrad : GradMemLpOn U (ENNReal.ofReal p) u.grad)
    (k : ℝ) (hk : 0 ≤ k) (i : Fin d) :
    eLpNormOn U (ENNReal.ofReal p)
        (fun x => (u.higherIntegrabilityClamp hU p hp hgrad k hk).grad x i) ≤
      eLpNormOn U (ENNReal.ofReal p) (fun x => u.grad x i) := by
  apply eLpNorm_mono
    ((u.higherIntegrabilityClamp hU p hp hgrad k hk).gradMemLp i).aestronglyMeasurable
  intro x
  rw [higherIntegrabilityClamp_grad hU p hp u hgrad k hk]
  change ‖({y | -k < u.toFun y ∧ u.toFun y < k}.indicator u.grad x) i‖ ≤
    ‖u.grad x i‖
  by_cases hx : x ∈ {y | -k < u.toFun y ∧ u.toFun y < k}
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Pi.zero_apply, norm_zero]
    exact norm_nonneg _

end H1Function

end PDE
