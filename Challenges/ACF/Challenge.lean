module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# The Alt-Caffarelli-Friedman monotonicity formula

Challenge: monotonicity (and finiteness) of the Alt-Caffarelli-Friedman functional of two
continuous, nonnegative, weakly subharmonic `H¹` functions with disjoint positivity sets, `d ≥ 3`.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, norm and balls are defined below (the norm inherited by `Vec d` from Mathlib
is the supremum norm, and `Metric.ball` is never used).  Sobolev functions are bundled together
with chosen representatives of the function and of its weak gradient.  The functional is valued in
`[0, ∞]` through lower Lebesgue integrals.
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


/-- Real `d × d` matrices acting on `Vec d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ


/-- Coordinate matrix-vector multiplication on `Mat d` and `Vec d`. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j


/-- A matrix-valued coefficient field on `Vec d`. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d


/-- Lebesgue volume restricted to a domain `U`. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U


/-- Scalar `L^p` membership on a domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)


/-- Scalar `L²` membership on a domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u


/-- Coordinatewise `L^p` membership of a vector field on a domain. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)


/-- Coordinatewise `L²` membership of a vector field on a domain. -/
abbrev GradMemL2On {d : ℕ}
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du


/-- A smooth compactly supported test function whose topological support lies inside `U`. -/
structure WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun

/-- The classical `i`th derivative of a test function. -/
noncomputable def WeakTestFunction.partialDeriv
    {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (x : Vec d) : ℝ :=
  (fderiv ℝ φ.toFun x) (basisVec i)

/-- The classical gradient of a test function. -/
noncomputable def WeakTestFunction.grad {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) : Vec d → Vec d :=
  fun x i => φ.partialDeriv i x


/-- A smooth compactly supported test function is pointwise nonnegative. -/
def WeakTestFunction.Nonnegative {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) : Prop :=
  ∀ x, 0 ≤ φ x


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


/-- An element of `H¹(U)`: a concrete scalar representative `toFun` and a chosen weak gradient
`grad`, both in `L²(U)`. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad


/-- Term-by-term integrability required to test the equation against a test function `φ`. -/
structure WeakDivergenceFormTestableOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) (φ : WeakTestFunction U) : Prop where
  flux_integrable :
    IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U
  source_integrable : IntegrableOn (fun x => f x * φ x) U
  forcing_integrable : IntegrableOn (fun x => vecDot (F x) (φ.grad x)) U


/-- Weak subsolution of `-div (a ∇u) ≤ f + div F` in `U`, tested against nonnegative smooth test
functions. -/
def IsWeakDivergenceFormSubsolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : WeakTestFunction U, φ.Nonnegative →
    WeakDivergenceFormTestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) ≤
        (∫ x in U, f x * φ x) -
          ∫ x in U, vecDot (F x) (φ.grad x)

/-- A homogeneous weak subsolution (`f = 0`, `F = 0`). -/
abbrev IsWeakDivergenceFormSubharmonicOn {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) : Prop :=
  IsWeakDivergenceFormSubsolutionOn a U u 0 0


/-- The Alt--Caffarelli--Friedman functional `r ↦ r⁻⁴ ∏_± ∫_{B_r} |∇u_±|² |x|^{2-d}`, valued
in `[0, ∞]` through lower Lebesgue integrals (no junk value for non-integrable integrands). -/
noncomputable def acfFunctional {d : ℕ} (Gp Gm : Vec d → Vec d) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (r⁻¹ ^ 4) *
    ((∫⁻ x in euclideanBall (0 : Vec d) r,
        ENNReal.ofReal (vecNormSq (Gp x) / vecEuclideanNorm x ^ (d - 2))) *
      ∫⁻ x in euclideanBall (0 : Vec d) r,
        ENNReal.ofReal (vecNormSq (Gm x) / vecEuclideanNorm x ^ (d - 2)))


/-- Alt--Caffarelli--Friedman monotonicity formula for `d ≥ 3`, with finiteness of the functional
(Theorem 2.13).  If `u₊, u₋ ∈ H¹(B_R)` are continuous, nonnegative, weakly subharmonic, vanish at
`0` and have disjoint positivity sets, then `r ↦ r⁻⁴ ∏_± ∫_{B_r} |∇u_±|² |x|^{2-d}` is monotone on
`(0, R)` and finite there. -/
theorem alt_caffarelli_friedman (d : ℕ) (hd : 3 ≤ d) (R : ℝ) (hR : 0 < R)
    (up um : H1Function (euclideanBall (0 : Vec d) R))
    (hup_cont : ContinuousOn up.toFun (euclideanBall (0 : Vec d) R))
    (hum_cont : ContinuousOn um.toFun (euclideanBall (0 : Vec d) R))
    (hup_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ up.toFun x)
    (hum_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ um.toFun x)
    (hup_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) up)
    (hum_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) um)
    (hup0 : up.toFun 0 = 0) (hum0 : um.toFun 0 = 0)
    (hdisj : ∀ x ∈ euclideanBall (0 : Vec d) R, up.toFun x * um.toFun x = 0) :
    MonotoneOn (acfFunctional up.grad um.grad) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R, acfFunctional up.grad um.grad r ≠ ⊤ := by
  sorry

end PDE
