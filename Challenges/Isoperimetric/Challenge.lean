module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The isoperimetric inequality

Challenge: the isoperimetric inequality for bounded open sets with `C¹` boundary in `ℝ^d`.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, squared norm and balls are defined below (the norm inherited by `Vec d`
from Mathlib is the supremum norm, and `Metric.ball` is never used).  Hausdorff measure is taken
on `HilbertVec d`, the same space with the Euclidean norm.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

open MeasureTheory

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- The Euclidean dot product on `Vec d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on `Vec d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- Euclidean squared distance on `Vec d`. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)

/-- The round Euclidean open ball of centre `x₀` and radius `R`. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The Euclidean space `ℝ^d` as a `PiLp 2` space, on which Hausdorff measure is taken. -/
abbrev HilbertVec (d : ℕ) :=
  PiLp 2 (fun _ : Fin d => ℝ)

/-- Put a vector of `Vec d` into `HilbertVec d`. -/
def Vec.toHilbertVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x

section C1Boundary

-- Keep the instance path used for `ContDiff ℝ 1 φ` and `fderiv ℝ φ y` on `Vec d` independent of
-- the inner-product-space imports needed for `HilbertVec` (both paths are definitionally equal).
attribute [-instance] InnerProductSpace.toNormedSpace

/-- `E` has `C¹` boundary: near every boundary point, `E` is the strict sublevel set `{φ < 0}`
of a `C¹` function with nowhere-vanishing derivative (equivalently, locally the open epigraph of a
`C¹` graph in rotated coordinates). -/
def HasC1Boundary {d : ℕ} (E : Set (Vec d)) : Prop :=
  ∀ x ∈ frontier E, ∃ W : Set (Vec d), IsOpen W ∧ x ∈ W ∧
    ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ y ∈ W, fderiv ℝ φ y ≠ 0) ∧
      E ∩ W = {y | y ∈ W ∧ φ y < 0}

end C1Boundary

/-- Isoperimetric inequality (Proposition 1.1, inequality part).  For a nonempty bounded open
set `E ⊆ ℝ^d` with `C¹` boundary, `d · ω_d^(1/d) · |E|^((d-1)/d) ≤ H^{d-1}(∂E)`, where `ω_d` is
the volume of the unit ball and `H^{d-1}` is the normalised Euclidean Hausdorff measure `μHE[d-1]`
on `HilbertVec d`. -/
theorem isoperimetric_inequality
    (d : ℕ) (hd : 1 ≤ d) (E : Set (Vec d))
    (hEopen : IsOpen E) (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty)
    (hE : HasC1Boundary E) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) *
        (volume E).toReal ^(((d : ℝ) - 1) / d)) ≤
      (μHE[d - 1] : Measure (HilbertVec d)) (Vec.toHilbertVec '' frontier E) := by
  sorry

end PDE
