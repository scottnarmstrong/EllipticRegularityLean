module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Meyers estimate

Challenge: Meyers' higher-integrability estimate for the gradient of weak solutions of `-div (a ∇u) = div f`
with measurable, uniformly elliptic, possibly nonsymmetric coefficients, with the explicit range of
exponents `2 + c / √Λ`: an interior estimate and a Dirichlet estimate.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, squared norm and balls are defined below (the norm inherited by `Vec d`
from Mathlib is the supremum norm, and `Metric.ball` is never used).  Sobolev functions are
bundled together with chosen representatives of the function and of its weak gradient.  Constants
are produced by existential statements, and the order of the quantifiers records what each constant
may depend on.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory

/-! ### Ambient space -/

/-- The coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on `Vec d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The Euclidean dot product on `Vec d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on `Vec d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- The Euclidean norm on `Vec d`. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

/-- Coordinate matrix-vector multiplication on `Mat d` and `Vec d`. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

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

/-! ### Coefficients -/

/-- A matrix-valued coefficient field on `Vec d`. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Nonsymmetric uniform ellipticity with constants `lam ≤ Lam`: `ξ · A ξ ≥ lam |ξ|²`, and the
inverse matrix satisfies `ξ · A⁻¹ ξ ≥ Lam⁻¹ |ξ|²` (which bounds `A` above by `Lam`). -/
def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

/-! ### Weak derivatives and Sobolev spaces -/

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

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- An element of `H¹₀(U)`: an `H¹(U)` function together with smooth compactly supported functions
`approx n` supported in `U` that converge to it, and their gradients to its gradient, in `L²(U)`. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => approx n x - toH1Function.toFun x)
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (approx n) x) (basisVec i) -
                toH1Function.grad x i)
            (2 : ℝ≥0∞) (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (H10Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function.toFun

/-! ### Weak solutions of divergence-form equations -/

/-- Term-by-term integrability required to test the equation against a test function `φ`. -/
structure WeakDivergenceFormTestableOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) (φ : WeakTestFunction U) : Prop where
  flux_integrable :
    IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U
  source_integrable : IntegrableOn (fun x => f x * φ x) U
  forcing_integrable : IntegrableOn (fun x => vecDot (F x) (φ.grad x)) U

/-- `u ∈ H¹(U)` is a weak solution of `-div (a ∇u) = f + div F` in `U`: every term is integrable
against every test function `φ`, and `∫ a∇u · ∇φ = ∫ f φ - ∫ F · ∇φ`. -/
def IsWeakDivergenceFormSolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : WeakTestFunction U,
    WeakDivergenceFormTestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) =
        (∫ x in U, f x * φ x) - ∫ x in U, vecDot (F x) (φ.grad x)

/-! ### Normalized norms -/

/-- Volume restricted to `U`, rescaled by the inverse volume of `U` (a probability measure when
`0 < volume U < ∞`). -/
noncomputable def normalizedVolumeOn {d : ℕ} (U : Set (Vec d)) :
    Measure (Vec d) :=
  (volume U)⁻¹ • volumeOn U

/-- The extended-real normalized `L^p` norm on `U`. -/
noncomputable def eLpMeanNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (normalizedVolumeOn U)

/-- The extended-real normalized `L^p` norm of the Euclidean magnitude of a vector field. -/
noncomputable def euclideanFieldELpMeanNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpMeanNormOn U p (fun x => vecEuclideanNorm (F x))

/-! ### The theorem -/

/-- The Meyers estimate with the range of exponents `2 + c / √Λ` (Theorem 4.4).  For `d ≥ 2` there are
constants `c, C > 0`, depending only on `d`, such that for every `Λ`, every measurable coefficient field `a`
on `B₁` with `IsEllipticMatrix 1 Λ (a x)` on `B₁`: (interior) for `2 ≤ p ≤ 2 + c/√Λ` every `H¹(B₁)` solution
of `-div (a ∇u) = div f` satisfies a normalized `L^p(B_{1/2})` bound on `√(∇u · a ∇u)` in terms of the
`L²(B₁)` norm of the same quantity and the `L^p(B₁)` norm of `f`; (Dirichlet) for
`(2 + c/√Λ)' ≤ p ≤ 2 + c/√Λ` every `H¹₀(B₁)` solution satisfies `‖∇u‖_{L^p(B₁)} ≤ C ‖f‖_{L^p(B₁)}`.
Norms are valued in `[0, ∞]`. -/
theorem exists_meyers_constants
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      (∀ (p : ℝ), 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
            (0 : Vec d → ℝ) f →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p)
              (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) ≤
            ENNReal.ofReal C *
              (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
                  (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) +
                euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal p) f)) ∧
      (∀ (p : ℝ), (2 + c / Real.sqrt Λ) / (1 + c / Real.sqrt Λ) ≤ p →
        p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
            u.toH1Function (0 : Vec d → ℝ) f →
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
            ENNReal.ofReal C *
              eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1))) := by
  sorry

end PDE
