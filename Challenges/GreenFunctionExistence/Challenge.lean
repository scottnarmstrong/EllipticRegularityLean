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
# Existence and uniqueness of the Green function, d ≥ 3

Challenge: existence, almost-everywhere uniqueness and basic properties of the Green function with pole at the
origin of `-div (a ∇ ·)` in the ball `B_R ⊂ ℝ^d`, `d ≥ 3` (Definition 4.39 and Proposition 4.40 of the
manuscript).  This is the companion of the `GreenFunctionBounds` challenge (Proposition 4.42): it shows
that the characterizing property `IsGreenFunction` is satisfied.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, squared norm and balls are defined below (the norm inherited by `Vec d`
from Mathlib is the supremum norm, and `Metric.ball` is never used).  Sobolev functions are
bundled together with chosen representatives of the function and of its weak gradient.  Constants
are produced by existential statements, and the order of the quantifiers records what each constant
may depend on.  The Green function is defined by its characterizing
property (`IsGreenFunction`): `G` is measurable, square integrable away from the origin, and for every `L²`
datum `g` vanishing near the origin, the ball averages of the `H¹₀` solution `v` of the adjoint problem
`-div (aᵀ ∇v) = g` converge to `∫ G g`.
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

/-- Coordinate matrix-vector multiplication on `Mat d` and `Vec d`. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

/-- Matrix transpose. -/
def matTranspose {d : ℕ} (A : Mat d) : Mat d :=
  Matrix.transpose A

/-- The `i`th coordinate basis vector. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

/-- Euclidean squared distance on `Vec d`. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)

/-- The round Euclidean open ball of centre `x₀` and radius `R`. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The round Euclidean closed ball of centre `x₀` and radius `R`. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

/-- Lebesgue volume restricted to a domain `U`. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

/-! ### Coefficients -/

/-- A matrix-valued coefficient field on `Vec d`. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- The transpose coefficient field. -/
abbrev transposeCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => matTranspose (a x)

/-- The adjoint coefficient field `aᵀ` of a divergence-form operator. -/
abbrev adjointCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  transposeCoeffField a

/-- Nonsymmetric uniform ellipticity with constants `lam ≤ Lam`: `ξ · A ξ ≥ lam |ξ|²`, and the
inverse matrix satisfies `ξ · A⁻¹ ξ ≥ Lam⁻¹ |ξ|²` (which bounds `A` above by `Lam`). -/
def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

/-- The integral average of `u` over `U`: `(volume U)⁻¹ ∫_U u` (total: junk value `0` when `volume U` is `0` or `∞`). -/
noncomputable def integralAverage {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, u x ∂volume

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

/-- Term-by-term integrability required to test the equation against an `H¹₀` function `φ`. -/
structure WeakDivergenceFormH10TestableOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) (φ : H10Function U) : Prop where
  flux_integrable :
    IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U
  source_integrable : IntegrableOn (fun x => f x * φ.toH1Function x) U
  forcing_integrable :
    IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U

/-- `u ∈ H¹(U)` solves `-div (a ∇u) = f + div F` in `U` tested against all `φ ∈ H¹₀(U)`: every term is
integrable and `∫ a∇u · ∇φ = ∫ f φ - ∫ F · ∇φ`. -/
def IsWeakDivergenceFormH10SolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    WeakDivergenceFormH10TestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) =
        (∫ x in U, f x * φ.toH1Function x) -
          ∫ x in U, vecDot (F x) (φ.toH1Function.grad x)

/-! ### The Green function -/

/-- Green function of `-div (a ∇ ·)` in `B_R` with pole at the origin (Definition 4.39).
`G` is measurable, in `L²(B_R \ B_ε)` for `ε ∈ (0,R)`, and for every `g ∈ L²(B_R)` vanishing
a.e. in some `B_ε` and every `H¹₀(B_R)` solution `v` of `-div (aᵗ ∇ v) = g`, the averages of `v`
over `B_ρ(0)` converge as `ρ → 0` to `∫ G g`. -/
def IsGreenFunction {d : ℕ} (a : CoeffField d) (R : ℝ) (G : Vec d → ℝ) : Prop :=
  Measurable G ∧
  (∀ ε : ℝ, 0 < ε → ε < R →
    MemL2On (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) G) ∧
  ∀ ε : ℝ, 0 < ε → ε < R → ∀ g : Vec d → ℝ,
    MemL2On (euclideanBall (0 : Vec d) R) g →
    (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) →
    ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
        v.toH1Function g (0 : Vec d → Vec d) →
      Filter.Tendsto (fun ρ : ℝ => integralAverage (euclideanBall (0 : Vec d) ρ) v.toH1Function.toFun)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in euclideanBall (0 : Vec d) R, G x * g x))

/-! ### The theorem -/

/-- Existence, uniqueness and basic properties of the Green function (Definition 4.39 and Proposition 4.40),
`d ≥ 3`.  There is `C₀ > 0`, depending only on `d`, such that for all `Λ`, `R > 0` and measurable coefficient
fields `a` on `B_R` with `IsEllipticMatrix 1 Λ (a x)` on `B_R`: a function `G` with `IsGreenFunction a R G`
exists; any two such functions agree almost everywhere on `B_R`; and every such `G` is nonnegative,
satisfies the Stampacchia bounds with constant `C₀` (independent of `Λ` and `R`), has a representative `Gc`
continuous on `B_R \ {0}` which is, away from the pole, an `H¹` weak solution of `-div (a ∇ ·) = 0`, and
satisfies the flux identity `∫_{B_R \ B_ε} ∇φ · a ∇G = φ(0)` for Lipschitz `φ` compactly supported in `B_R`
and constant on `B_ε`. -/
theorem greenExists (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      (∃ G : Vec d → ℝ, IsGreenFunction a R G) ∧
      (∀ G G' : Vec d → ℝ, IsGreenFunction a R G → IsGreenFunction a R G' →
        G =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G') ∧
      ∀ G : Vec d → ℝ, IsGreenFunction a R G →
        (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ G x) ∧
        (IntegrableOn G (euclideanBall (0 : Vec d) R) ∧
          ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) R →
            ∫⁻ x in E, ENNReal.ofReal (G x) ≤
              ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d))) ∧
        (∀ t : ℝ, 0 < t →
          volume {x ∈ euclideanBall (0 : Vec d) R | t < G x} ≤
            ENNReal.ofReal ((C₀ / t) ^ ((d : ℝ) / ((d : ℝ) - 2)))) ∧
        (∃ Gc : Vec d → ℝ,
          ContinuousOn Gc (euclideanBall (0 : Vec d) R \ {0}) ∧
          Gc =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G ∧
          ∀ ε : ℝ, 0 < ε → ε < R →
            ∃ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε),
              H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε)] G ∧
              IsWeakDivergenceFormSolutionOn a
                (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) H
                (0 : Vec d → ℝ) (0 : Vec d → Vec d)) ∧
        (∀ ε : ℝ, 0 < ε → ε < R →
          ∀ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)),
          H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2))] G →
          ∀ φ : Vec d → ℝ, (∃ K : NNReal, LipschitzWith K φ) → HasCompactSupport φ →
            tsupport φ ⊆ euclideanBall (0 : Vec d) R →
            (∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) ε, φ x = c) →
            ∫ x in euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε,
                vecDot (fun i => fderiv ℝ φ x (basisVec i)) (matVecMul (a x) (H.grad x)) = φ 0) := by
  sorry

end PDE
