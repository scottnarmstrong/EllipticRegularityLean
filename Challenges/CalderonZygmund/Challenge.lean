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
# The Calderón–Zygmund estimate for divergence-form equations

Challenge: the `L^p` gradient estimate (`p ≥ 2`) for weak solutions of `-div (a ∇u) = div F` in the
unit ball of `ℝ^d` whose measurable, uniformly elliptic coefficients are within `1 / (C p)` of their
ball average in Euclidean operator norm.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, squared norm and balls are defined below (the norm inherited by `Vec d`
from Mathlib is the supremum norm, and `Metric.ball` is never used).  Sobolev functions are
bundled together with chosen representatives of the function and of its weak gradient.  Constants
are produced by existential statements, and the order of the quantifiers records what each constant
may depend on.  The normalized `L^p` norms of vector fields are real
numbers only for functions known to lie in the corresponding space, so the statement passes membership
proofs (`memLp_normalizedVolumeOn_of_memLpOn`, `volume_euclideanBall_pos`) to them; these two small
lemmas, and the topological facts they rest on, are proved in this file.
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

/-- `A` is within Euclidean operator distance `delta` of `B`. -/
def IsMatrixPerturbationLE {d : ℕ} (delta : ℝ) (A B : Mat d) : Prop :=
  ∀ xi : Vec d,
    vecEuclideanNorm (matVecMul (A - B) xi) ≤ delta * vecEuclideanNorm xi

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

/-- An element of `W^{1,p}(U)`: a concrete representative `toFun` and a chosen weak gradient `grad`,
both in `L^p(U)`. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

/-- Membership of a concrete function in `W^{1,p}(U)`: it is the representative of some `W1pFunction`. -/
def MemW1p {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  ∃ v : W1pFunction U p, v.toFun = u

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

/-- The real normalized `L^p` norm, available only for functions known to lie in normalized `L^p`. -/
noncomputable def lpMeanNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MemLp f p (normalizedVolumeOn U)) : ℝ :=
  let finiteNorm : {q : ℝ≥0∞ // q ≠ ∞} :=
    ⟨eLpMeanNormOn U p f, ne_of_lt <| by
      simpa only [eLpMeanNormOn] using hf.eLpNorm_lt_top⟩
  finiteNorm.1.toReal

/-- The real normalized `L^p` norm of the Euclidean magnitude of a vector field. -/
noncomputable def euclideanFieldLpMeanNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p
      (normalizedVolumeOn U)) : ℝ :=
  lpMeanNormOn U p (fun x => vecEuclideanNorm (F x)) hF

/-! ### Positivity of ball volumes -/

section

-- The smoothness lemmas below are stated for `Vec d` with the instance path that does not go through
-- `InnerProductSpace.toNormedSpace` or `RCLike.toNormedAlgebra` (both paths are definitionally equal).
attribute [-instance] InnerProductSpace.toNormedSpace RCLike.toNormedAlgebra

/-- The squared Euclidean norm is smooth. -/
theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) fun i _hi =>
    (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

/-- The squared Euclidean distance to a fixed point is smooth. -/
theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)

/-- The squared Euclidean distance to a fixed point is continuous. -/
theorem continuous_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    Continuous (fun x : Vec d => euclideanSqDist x x₀) :=
  (contDiff_euclideanSqDist_left x₀).continuous

open Set in
/-- Euclidean open balls are open. -/
theorem isOpen_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsOpen (euclideanBall x₀ R) := by
  change IsOpen
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iio (R ^ 2))
  exact isOpen_Iio.preimage (continuous_euclideanSqDist_left x₀)

end

/-- The squared Euclidean distance from a point to itself is zero. -/
@[simp]
theorem euclideanSqDist_self {d : ℕ} (x : Vec d) :
    euclideanSqDist x x = 0 := by
  simp [euclideanSqDist, vecNormSq, vecDot]

/-- The centre of a Euclidean ball of positive radius lies in it. -/
theorem center_mem_euclideanBall {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    x₀ ∈ euclideanBall x₀ R := by
  change euclideanSqDist x₀ x₀ < R ^ 2
  rw [euclideanSqDist_self]
  exact sq_pos_of_pos hR

/-- Euclidean balls of positive radius are nonempty. -/
theorem euclideanBall_nonempty {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    (euclideanBall x₀ R).Nonempty :=
  ⟨x₀, center_mem_euclideanBall x₀ hR⟩

/-- Euclidean balls of positive radius have positive volume. -/
theorem volume_euclideanBall_pos {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < volume (euclideanBall x R) :=
  (isOpen_euclideanBall x R).measure_pos volume
    (euclideanBall_nonempty x hR)

/-- `L^p` membership for the restricted volume passes to the normalized restricted volume on a set
of positive volume. -/
theorem memLp_normalizedVolumeOn_of_memLpOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f : Vec d → E}
    (hf : MemLp f p (volumeOn U))
    (hUPos : 0 < volume U) :
    MemLp f p (normalizedVolumeOn U) := by
  rw [normalizedVolumeOn]
  exact hf.smul_measure
    (ENNReal.inv_ne_top.mpr hUPos.ne')

/-! ### The theorem -/

/-- The Calderón–Zygmund estimate (Proposition 3.4).  For `Λ ≥ 1` there is a constant `C ≥ 1` such that for
every `p ≥ 2`, every measurable coefficient field `a` on the unit ball `B₁` with `IsEllipticMatrix 1 Λ (a x)`
for a.e. `x` and with `a x` within `1 / (C p)` of its ball average `A₀` (in Euclidean operator norm) for
a.e. `x`, every `u ∈ H¹(B₁)` solving `-div (a ∇u) = div F` with `F ∈ L^p(B₁)` lies in `W^{1,p}(B_{1/2})`, and
`‖∇u‖_{L^p(B_{1/2})} ≤ C (‖∇u‖_{L²(B₁)} + p ‖F‖_{L^p(B₁)})` (normalized `L^p` norms). -/
theorem exists_calderonZygmund
    (d : ℕ) (hd : 0 < d) (Lambda : ℝ) (hLambda : 1 ≤ Lambda) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsEllipticMatrix 1 Lambda (a x)) →
      (let A0 : Mat d := fun i j =>
          integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => a x i j)
        ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
          IsMatrixPerturbationLE (1 / (C * p)) (a x) A0) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  sorry

end PDE
