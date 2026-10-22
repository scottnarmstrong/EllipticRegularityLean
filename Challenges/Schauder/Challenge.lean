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

/-!
# The C^{0,1-} Schauder estimate

Challenge: Hölder regularity, with the explicit dependence on the exponent `α ∈ (0,1)`, of weak
solutions of `-div (a ∇u) = div F` in the unit ball when `a` is a small measurable perturbation of
the identity.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, norm and balls are defined below (the norm inherited by `Vec d` from Mathlib
is the supremum norm, and `Metric.ball` is never used).  Sobolev functions are bundled together
with chosen representatives of the function and of its weak gradient.  The constant `C` is chosen
depending only on `d`, before `α`, `a`, `u` and `F`.
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


/-- `u ∈ H¹(U)` is a weak solution of `-div (a ∇u) = f + div F` in `U`: every term is integrable
against every test function `φ`, and `∫ a∇u · ∇φ = ∫ f φ - ∫ F · ∇φ`. -/
def IsWeakDivergenceFormSolutionOn {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : WeakTestFunction U,
    WeakDivergenceFormTestableOn a U u f F φ ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) =
        (∫ x in U, f x * φ x) - ∫ x in U, vecDot (F x) (φ.grad x)


/-- A Hölder-seminorm bound using the explicit Euclidean magnitude on `Vec d`, rather than its
inherited supremum norm. -/
def EuclideanHolderSeminormLE {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |u x - u y| ≤ K * vecEuclideanNorm (x - y) ^ α

/-- A Euclidean Hölder representative together with its a.e. agreement on the stated set. -/
def HasEuclideanHolderRepresentativeOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (α K : ℝ) : Prop :=
  ∃ representative : Vec d → ℝ,
    representative =ᵐ[volumeOn U] u ∧
      EuclideanHolderSeminormLE U representative α K


/-- `A` is within Euclidean operator distance `delta` of `B`. -/
def IsMatrixPerturbationLE {d : ℕ} (delta : ℝ) (A B : Mat d) : Prop :=
  ∀ xi : Vec d,
    vecEuclideanNorm (matVecMul (A - B) xi) ≤ delta * vecEuclideanNorm xi


/-- The extended-real `L^p` norm with respect to volume restricted to `U`. -/
noncomputable def eLpNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (volumeOn U)

/-- The real `L^p` norm on restricted volume, guarded by membership in `L^p`. -/
noncomputable def lpNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MemLp f p (volumeOn U)) : ℝ :=
  let finiteNorm : {q : ℝ≥0∞ // q ≠ ∞} :=
    ⟨eLpNormOn U p f, ne_of_lt <| by
      simpa only [eLpNormOn] using hf.eLpNorm_lt_top⟩
  finiteNorm.1.toReal

/-- The guarded real restricted `L^p` norm of a vector field's Euclidean magnitude. -/
noncomputable def euclideanFieldLpNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p (volumeOn U)) : ℝ :=
  lpNormOn U p (fun x => vecEuclideanNorm (F x)) hF


/-- The `C^{0,1-}` Schauder estimate (Proposition 3.1).  For `d ≥ 1` there is `C = C(d) > 0` such
that for every `α ∈ (0,1)`, every measurable coefficient field `a` on `B₁` within distance
`2^{-3-d/2} (1-α)` of the identity, every `F ∈ L^{d/(1-α)}(B₁)`, and every weak solution
`u ∈ H¹(B₁)` of `-div (a ∇u) = div F`, the function `u` has a Hölder representative on `B_{1/2}`
with seminorm at most `(C/α) (‖∇u‖_{L²(B₁)} + (1-α)⁻¹ ‖F‖_{L^{d/(1-α)}(B₁)})`. -/
theorem exists_schauderCalpha_constant {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {a : CoeffField d} (u : H1Function (euclideanBall (0 : Vec d) 1))
        {F : Vec d → Vec d},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE ((2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)) (a x) 1) →
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal ((d : ℝ) / (1 - α))) (volumeOn (euclideanBall (0 : Vec d) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u.toFun α
        ((C / α) * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF / (1 - α)))  := by
  sorry

end PDE
