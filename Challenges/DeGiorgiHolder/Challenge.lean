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
# De Giorgi's interior Hölder estimate

Challenge: the interior Hölder estimate of De Giorgi for weak solutions of `-div (a ∇u) = 0` in the unit
ball of `ℝ^d` (`d ≥ 3`), with measurable, uniformly elliptic, possibly nonsymmetric coefficients, with the
explicit dependence of the Hölder exponent and constant on the ellipticity ratio.

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

/-! ### Hölder seminorm -/

/-- A Hölder-seminorm bound with the Euclidean norm: `|u x - u y| ≤ K |x - y|^α` on `U`. -/
def EuclideanHolderSeminormLE {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |u x - u y| ≤ K * vecEuclideanNorm (x - y) ^ α

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

/-! ### The theorem -/

/-- De Giorgi's interior Hölder estimate (Theorem 4.8).  For `d ≥ 3` there is `C > 0`, depending only on `d`,
such that for every `Λ ≥ 1` there is an exponent `α ∈ (0, 1]` with `exp (-C Λ^{(d+2)/4}) ≤ α` such that for every
measurable coefficient field `a` on `B₁` with `IsEllipticMatrix 1 Λ (a x)` on `B₁` and every weak solution
`u ∈ H¹(B₁)` of `-div (a ∇u) = 0`, there is a representative `v` of `u` on `B_{1/2}` with `|v| ≤ M₀` and
Hölder seminorm at most `M₁` (exponent `α`) on `B_{1/2}`, where `M₀ + M₁ ≤ C Λ^{d/4} ‖u‖_{L²(B₁)}`. -/
theorem exists_deGiorgi_holder_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤ ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  sorry

end PDE
