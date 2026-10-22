module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The sharp Sobolev inequality for `p = 1`

Challenge: `‖u‖_{L^{d/(d-1)}(ℝ^d)} ≤ d⁻¹ |B₁|^{-1/d} ‖∇u‖_{L¹(ℝ^d)}` for `u ∈ W^{1,1}(ℝ^d)`.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, norm and balls are defined below (the norm inherited by `Vec d` from Mathlib
is the supremum norm, and `Metric.ball` is never used).  A Sobolev function is bundled together
with a chosen representative of the function and of its weak gradient.
-/

@[expose] public section

open scoped BigOperators ENNReal Topology

namespace PDE

open MeasureTheory Filter

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ


/-- The Euclidean dot product on `Vec d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i


/-- The square of the Euclidean norm on `Vec d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x


/-- The Euclidean norm on `Vec d`. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)


/-- The `i`th coordinate basis vector. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)


/-- Euclidean squared distance on `Vec d`. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)


/-- The round Euclidean open ball of centre `x₀` and radius `R`. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}


/-- Lebesgue volume restricted to a domain `U`. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U


/-- Scalar `L^p` membership on a domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)


/-- Coordinatewise `L^p` membership of a vector field on a domain. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)


/-- `gi` is the `i`th weak derivative of `u` on `U`. -/
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

/-- `Du` is a (coordinatewise) weak gradient of `u` on `U`. -/
def HasWeakGradientOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)


/-- An element of `W^{1,p}(U)`: a concrete scalar representative `toFun` and a chosen weak
gradient `grad`, both in `L^p(U)`. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad


/-- Sharp Sobolev inequality for `p = 1` (Proposition 1.4):
`‖u‖_{L^{d/(d-1)}(ℝ^d)} ≤ d⁻¹ |B₁|^{-1/d} ‖∇u‖_{L¹(ℝ^d)}`.  The exponent `d/(d-1)` is taken in
`[1,∞]`, so `d = 1` reads `‖u‖_∞ ≤ ½ ‖u'‖_{L¹}`. -/
theorem sobolev_inequality_sharp_p_one
    (d : ℕ) (hd : 1 ≤ d) (u : W1pFunction (Set.univ : Set (Vec d)) 1) :
    eLpNorm u.toFun ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤
      ENNReal.ofReal (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 1 volume := by
  sorry

end PDE
