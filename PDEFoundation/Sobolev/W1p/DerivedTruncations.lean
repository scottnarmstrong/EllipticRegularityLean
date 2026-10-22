module

public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Derived one-sided truncations in `W^{1,p}`

This module derives the negative part and maximum with a constant from the
positive-part truncation.  The formulas retain literal representatives and
coordinatewise `L^p` contraction estimates with constant one.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The negative part relative to `c`, namely `(c - u)₊`. -/
noncomputable def negativePartConstSub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    W1pFunction U p :=
  (-u).positivePartSubConst hU hp hpTop (-c)

@[simp]
theorem negativePartConstSub_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.negativePartConstSub hU hp hpTop c).toFun =
      fun x => max (c - u.toFun x) 0 := by
  funext x
  change max ((-u).toFun x - -c) 0 = max (c - u.toFun x) 0
  simp only [neg_toFun]
  congr 1
  ring

@[simp]
theorem negativePartConstSub_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.negativePartConstSub hU hp hpTop c).grad =
      fun x => {y | u.toFun y < c}.indicator (-u.grad) x := by
  funext x
  change {y | -c < (-u).toFun y}.indicator (-u).grad x =
    {y | u.toFun y < c}.indicator (-u.grad) x
  by_cases hx : u.toFun x < c
  · have hx' : -c < (-u).toFun x := by
      simp only [neg_toFun]
      linarith
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx,
      ite_eq_left hx', Pi.neg_apply]
    rfl
  · have hxNot : x ∉ {y | u.toFun y < c} := hx
    have hx' : ¬ -c < (-u).toFun x := by
      simp only [neg_toFun, not_lt] at hx ⊢
      linarith
    have hx'Not : x ∉ {y | -c < (-u).toFun y} := hx'
    simp only [Set.indicator_apply, ite_eq_right hxNot, ite_eq_right hx'Not]

/-- Negative-part truncation contracts every native coordinate-gradient
seminorm with constant one. -/
theorem eLpNormOn_negativePartConstSub_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) (i : Fin d) :
    eLpNormOn U p
        (fun x =>
          (u.negativePartConstSub hU hp hpTop c).grad x i) ≤
      eLpNormOn U p (fun x => u.grad x i) := by
  apply eLpNorm_mono
    ((u.negativePartConstSub hU hp hpTop c).gradMemLp i).aestronglyMeasurable
  intro x
  rw [negativePartConstSub_grad hU hp hpTop u c]
  by_cases hx : u.toFun x < c
  · have hxMem : x ∈ {y | u.toFun y < c} := hx
    change ‖({y | u.toFun y < c}.indicator (-u.grad) x) i‖ ≤
      ‖u.grad x i‖
    rw [Set.indicator_of_mem hxMem]
    change ‖-(u.grad x i)‖ ≤ ‖u.grad x i‖
    rw [norm_neg]
  · have hxNotMem : x ∉ {y | u.toFun y < c} := hx
    change ‖({y | u.toFun y < c}.indicator (-u.grad) x) i‖ ≤
      ‖u.grad x i‖
    rw [Set.indicator_of_notMem hxNotMem, Pi.zero_apply]
    simpa only [norm_zero] using norm_nonneg (u.grad x i)

/-- Pointwise maximum of a representative-level Sobolev function and a
constant, with the literal positive-part gradient representative. -/
noncomputable def maxConst
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    W1pFunction U p := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  exact (u.positivePartSubConst hU hp hpTop c).addConst c

@[simp]
theorem maxConst_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.maxConst hU hp hpTop c).toFun =
      fun x => max (u.toFun x) c := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  funext x
  change max (u.toFun x - c) 0 + c = max (u.toFun x) c
  rcases le_total (u.toFun x - c) 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith)]
    ring

@[simp]
theorem maxConst_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.maxConst hU hp hpTop c).grad =
      fun x => {y | c < u.toFun y}.indicator u.grad x := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  change
    ((u.positivePartSubConst hU hp hpTop c).addConst c).grad =
      fun x => {y | c < u.toFun y}.indicator u.grad x
  funext x
  rw [addConst_grad]
  rfl

/-- Taking the maximum with a constant contracts every native
coordinate-gradient seminorm with constant one. -/
theorem eLpNormOn_maxConst_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) (i : Fin d) :
    eLpNormOn U p (fun x => (u.maxConst hU hp hpTop c).grad x i) ≤
      eLpNormOn U p (fun x => u.grad x i) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  rw [maxConst_grad hU hp hpTop u c]
  exact u.eLpNormOn_positivePartSubConst_grad_coord_le hU hp hpTop c i

end W1pFunction

end PDE
