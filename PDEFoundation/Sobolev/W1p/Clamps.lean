module

public import PDEFoundation.Sobolev.W1p.DerivedTruncations

/-!
# Minimum and two-sided truncation in `W^{1,p}`

This file derives minimum with a constant and interval truncation from the
one-sided truncation API. For `a ≤ b`, the interval truncation has the exact
gradient

`1_{\{a < u\} ∩ \{u < b\}} ∇u`.

All coordinate-gradient estimates retain contraction constant one.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Pointwise minimum of a Sobolev representative and a constant. -/
noncomputable def minConst
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    W1pFunction U p :=
  -((-u).maxConst hU hp hpTop (-c))

@[simp]
theorem minConst_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.minConst hU hp hpTop c).toFun =
      fun x => min (u.toFun x) c := by
  rw [minConst, neg_toFun, maxConst_toFun]
  funext x
  simp only [neg_toFun]
  rcases le_total (u.toFun x) c with h | h
  · rw [min_eq_left h, max_eq_left (neg_le_neg h), neg_neg]
  · rw [min_eq_right h, max_eq_right (neg_le_neg h), neg_neg]

@[simp]
theorem minConst_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    (u.minConst hU hp hpTop c).grad =
      fun x => {y | u.toFun y < c}.indicator u.grad x := by
  rw [minConst, neg_grad, maxConst_grad]
  funext x
  by_cases hx : u.toFun x < c
  · have hx' : -c < (-u).toFun x := by
      simp only [neg_toFun]
      linarith
    simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      hx, hx', ite_true]
    exact neg_neg (u.grad x)
  · have hx' : ¬ -c < (-u).toFun x := by
      simp only [neg_toFun, not_lt] at hx ⊢
      linarith
    simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      hx, hx', ite_false, neg_zero]

/-- Taking the minimum with a constant contracts every native
coordinate-gradient seminorm with constant one. -/
theorem eLpNormOn_minConst_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) (i : Fin d) :
    eLpNormOn U p
        (fun x => (u.minConst hU hp hpTop c).grad x i) ≤
      eLpNormOn U p (fun x => u.grad x i) := by
  apply eLpNorm_mono ((u.minConst hU hp hpTop c).gradMemLp i).aestronglyMeasurable
  intro x
  rw [minConst_grad hU hp hpTop u c]
  by_cases hx : u.toFun x < c
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      hx, ite_true]
    exact le_rfl
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      hx, ite_false, Pi.zero_apply]
    simpa only [norm_zero] using norm_nonneg (u.grad x i)

/-- Interval truncation `min (max u a) b`. -/
noncomputable def clampConst
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (a b : ℝ) :
    W1pFunction U p :=
  (u.maxConst hU hp hpTop a).minConst hU hp hpTop b

@[simp]
theorem clampConst_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (a b : ℝ) :
    (u.clampConst hU hp hpTop a b).toFun =
      fun x => min (max (u.toFun x) a) b := by
  rw [clampConst, minConst_toFun]
  funext x
  rw [maxConst_toFun]

@[simp]
theorem clampConst_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (a b : ℝ) :
    (u.clampConst hU hp hpTop a b).grad =
      fun x =>
        {y | a < u.toFun y ∧ u.toFun y < b}.indicator u.grad x := by
  rw [clampConst, minConst_grad]
  funext x
  by_cases hxa : a < u.toFun x
  · have hmax : max (u.toFun x) a = u.toFun x :=
      max_eq_left hxa.le
    simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      maxConst_toFun, maxConst_grad, hmax, hxa,
      true_and, ite_true]
  · have huxle : u.toFun x ≤ a := le_of_not_gt hxa
    have hmax : max (u.toFun x) a = a :=
      max_eq_right huxle
    simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      maxConst_toFun, maxConst_grad, hmax, hxa,
      false_and, ite_false, ite_self]

/-- Interval truncation contracts every native coordinate-gradient seminorm
with constant one. -/
theorem eLpNormOn_clampConst_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (a b : ℝ) (i : Fin d) :
    eLpNormOn U p
        (fun x => (u.clampConst hU hp hpTop a b).grad x i) ≤
      eLpNormOn U p (fun x => u.grad x i) :=
  (u.maxConst hU hp hpTop a).eLpNormOn_minConst_grad_coord_le
    hU hp hpTop b i |>.trans
      (u.eLpNormOn_maxConst_grad_coord_le hU hp hpTop a i)

end W1pFunction

end PDE
