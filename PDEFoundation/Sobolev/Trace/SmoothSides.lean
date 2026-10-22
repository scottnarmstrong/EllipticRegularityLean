module

public import PDEFoundation.Geometry.SquareLoop
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smooth scalar restrictions to square sides

The side parameters in this file are the increasing Cartesian coordinates.
Thus all four raw side restrictions have the positive corresponding coordinate
derivative. The top and left sides acquire a minus sign only after composing
with the decreasing parameter used by `squareLoop`.
-/

@[expose] public section

namespace PDE

noncomputable section

/-- The scalar restriction to the right side, parametrized by increasing
vertical coordinate. -/
def squareLoopRightRestriction (u : Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => u (squareLoopRightSide x₀ r t)

/-- The scalar restriction to the top side, parametrized by increasing
horizontal coordinate. -/
def squareLoopTopRestriction (u : Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => u (squareLoopTopSide x₀ r t)

/-- The scalar restriction to the left side, parametrized by increasing
vertical coordinate. -/
def squareLoopLeftRestriction (u : Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => u (squareLoopLeftSide x₀ r t)

/-- The scalar restriction to the bottom side, parametrized by increasing
horizontal coordinate. -/
def squareLoopBottomRestriction (u : Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => u (squareLoopBottomSide x₀ r t)

theorem contDiff_squareLoopRightSide (x₀ : Vec 2) (r : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (squareLoopRightSide x₀ r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa only [squareLoopRightSide_zero] using!
      (contDiff_const : ContDiff ℝ n fun _ : ℝ => x₀ 0 + r)
  · simpa only [squareLoopRightSide_one] using! (contDiff_id : ContDiff ℝ n fun t : ℝ => t)

theorem contDiff_squareLoopTopSide (x₀ : Vec 2) (r : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (squareLoopTopSide x₀ r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa only [squareLoopTopSide_zero] using! (contDiff_id : ContDiff ℝ n fun t : ℝ => t)
  · simpa only [squareLoopTopSide_one] using! (contDiff_const : ContDiff ℝ n fun _ : ℝ => x₀ 1 + r)

theorem contDiff_squareLoopLeftSide (x₀ : Vec 2) (r : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (squareLoopLeftSide x₀ r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa only [squareLoopLeftSide_zero] using! (contDiff_const : ContDiff ℝ n fun _ : ℝ => x₀ 0 - r)
  · simpa only [squareLoopLeftSide_one] using! (contDiff_id : ContDiff ℝ n fun t : ℝ => t)

theorem contDiff_squareLoopBottomSide (x₀ : Vec 2) (r : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (squareLoopBottomSide x₀ r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa only [squareLoopBottomSide_zero] using! (contDiff_id : ContDiff ℝ n fun t : ℝ => t)
  · simpa only [squareLoopBottomSide_one] using!
      (contDiff_const : ContDiff ℝ n fun _ : ℝ => x₀ 1 - r)

theorem contDiff_squareLoopRightRestriction {u : Vec 2 → ℝ} {n : ℕ∞}
    (hu : ContDiff ℝ n u) (x₀ : Vec 2) (r : ℝ) :
    ContDiff ℝ n (squareLoopRightRestriction u x₀ r) := by
  exact hu.comp (contDiff_squareLoopRightSide x₀ r)

theorem contDiff_squareLoopTopRestriction {u : Vec 2 → ℝ} {n : ℕ∞}
    (hu : ContDiff ℝ n u) (x₀ : Vec 2) (r : ℝ) :
    ContDiff ℝ n (squareLoopTopRestriction u x₀ r) := by
  exact hu.comp (contDiff_squareLoopTopSide x₀ r)

theorem contDiff_squareLoopLeftRestriction {u : Vec 2 → ℝ} {n : ℕ∞}
    (hu : ContDiff ℝ n u) (x₀ : Vec 2) (r : ℝ) :
    ContDiff ℝ n (squareLoopLeftRestriction u x₀ r) := by
  exact hu.comp (contDiff_squareLoopLeftSide x₀ r)

theorem contDiff_squareLoopBottomRestriction {u : Vec 2 → ℝ} {n : ℕ∞}
    (hu : ContDiff ℝ n u) (x₀ : Vec 2) (r : ℝ) :
    ContDiff ℝ n (squareLoopBottomRestriction u x₀ r) := by
  exact hu.comp (contDiff_squareLoopBottomSide x₀ r)

private theorem hasDerivAt_squareLoopRightSide (x₀ : Vec 2) (r t : ℝ) :
    HasDerivAt (squareLoopRightSide x₀ r) (basisVec (1 : Fin 2)) t := by
  convert
    ((hasDerivAt_id t).smul_const (basisVec (1 : Fin 2))).const_add
      (squarePoint (x₀ 0 + r) 0) using 1
  · funext s i
    fin_cases i <;> simp [squareLoopRightSide, squarePoint, basisVec]
  · simp

private theorem hasDerivAt_squareLoopTopSide (x₀ : Vec 2) (r t : ℝ) :
    HasDerivAt (squareLoopTopSide x₀ r) (basisVec (0 : Fin 2)) t := by
  convert
    ((hasDerivAt_id t).smul_const (basisVec (0 : Fin 2))).add_const
      (squarePoint 0 (x₀ 1 + r)) using 1
  · funext s i
    fin_cases i <;> simp [squareLoopTopSide, squarePoint, basisVec]
  · simp

private theorem hasDerivAt_squareLoopLeftSide (x₀ : Vec 2) (r t : ℝ) :
    HasDerivAt (squareLoopLeftSide x₀ r) (basisVec (1 : Fin 2)) t := by
  convert
    ((hasDerivAt_id t).smul_const (basisVec (1 : Fin 2))).const_add
      (squarePoint (x₀ 0 - r) 0) using 1
  · funext s i
    fin_cases i <;> simp [squareLoopLeftSide, squarePoint, basisVec]
  · simp

private theorem hasDerivAt_squareLoopBottomSide (x₀ : Vec 2) (r t : ℝ) :
    HasDerivAt (squareLoopBottomSide x₀ r) (basisVec (0 : Fin 2)) t := by
  convert
    ((hasDerivAt_id t).smul_const (basisVec (0 : Fin 2))).add_const
      (squarePoint 0 (x₀ 1 - r)) using 1
  · funext s i
    fin_cases i <;> simp [squareLoopBottomSide, squarePoint, basisVec]
  · simp

theorem deriv_squareLoopRightRestriction {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ : Vec 2) (r t : ℝ) :
    deriv (squareLoopRightRestriction u x₀ r) t =
      classicalGradient u (squareLoopRightSide x₀ r t) 1 := by
  have h := HasFDerivAt.comp_hasDerivAt t
    ((hu.differentiable (by norm_num) (squareLoopRightSide x₀ r t)).hasFDerivAt)
    (hasDerivAt_squareLoopRightSide x₀ r t)
  simpa only [squareLoopRightRestriction, Function.comp_apply,
    classicalGradient_apply] using! h.deriv

theorem deriv_squareLoopTopRestriction {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ : Vec 2) (r t : ℝ) :
    deriv (squareLoopTopRestriction u x₀ r) t =
      classicalGradient u (squareLoopTopSide x₀ r t) 0 := by
  have h := HasFDerivAt.comp_hasDerivAt t
    ((hu.differentiable (by norm_num) (squareLoopTopSide x₀ r t)).hasFDerivAt)
    (hasDerivAt_squareLoopTopSide x₀ r t)
  simpa only [squareLoopTopRestriction, Function.comp_apply,
    classicalGradient_apply] using! h.deriv

theorem deriv_squareLoopLeftRestriction {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ : Vec 2) (r t : ℝ) :
    deriv (squareLoopLeftRestriction u x₀ r) t =
      classicalGradient u (squareLoopLeftSide x₀ r t) 1 := by
  have h := HasFDerivAt.comp_hasDerivAt t
    ((hu.differentiable (by norm_num) (squareLoopLeftSide x₀ r t)).hasFDerivAt)
    (hasDerivAt_squareLoopLeftSide x₀ r t)
  simpa only [squareLoopLeftRestriction, Function.comp_apply,
    classicalGradient_apply] using! h.deriv

theorem deriv_squareLoopBottomRestriction {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ : Vec 2) (r t : ℝ) :
    deriv (squareLoopBottomRestriction u x₀ r) t =
      classicalGradient u (squareLoopBottomSide x₀ r t) 0 := by
  have h := HasFDerivAt.comp_hasDerivAt t
    ((hu.differentiable (by norm_num) (squareLoopBottomSide x₀ r t)).hasFDerivAt)
    (hasDerivAt_squareLoopBottomSide x₀ r t)
  simpa only [squareLoopBottomRestriction, Function.comp_apply,
    classicalGradient_apply] using! h.deriv

end

end PDE
