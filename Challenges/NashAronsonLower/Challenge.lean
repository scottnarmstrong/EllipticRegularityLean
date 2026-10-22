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
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Nash–Aronson lower bound

Challenge: the Gaussian lower bound of Nash and Aronson for the fundamental solution of
`∂ₜu - div (a ∇u) = 0` on `ℝ^d × [s, t]`, stated without the kernel: for nonnegative `L¹ ∩ L²` data `f`
(initial) and `g` (test) supported in balls of radius `√(t - s)/8` about `y` and `x`, the energy solution
`u` of the Cauchy problem with datum `f` satisfies
`c (t - s)^{-d/2} exp (-β |x - y|² / (t - s)) (∫ f) (∫ g) ≤ ∫ g u(·, t)`.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure, and space-time by
`Vec d × ℝ`; the explicit Euclidean dot product, squared norm and balls are defined below (the norm
inherited by `Vec d` from Mathlib is the supremum norm, and `Metric.ball` is never used).  Solutions
are taken in the parabolic energy space `ParH1Function U I` (Definition 5.1 of the manuscript);
`IsCauchySolution` asks for a weak solution on `ℝ^d × [s, T]` whose every-time slice at time `s` is
`f` almost everywhere.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory Set

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

/-! ### Parabolic coefficients, energy space and weak solutions -/

/-- Time-dependent coefficient field on space-time. -/
abbrev ParCoeffField (d : ℕ) := Vec d × ℝ → Mat d

/-- The parabolic coefficient hypotheses (manuscript (5.1)) on `U × I`: jointly measurable
entries, `0 < λ ≤ Λ`, and for a.e. `(x,t)` both `e·a e ≥ λ|e|²` and `e·a⁻¹e ≥ Λ⁻¹|e|²`
(this is `IsEllipticMatrix λ Λ (a z)`). -/
structure IsParabolicCoeff {d : ℕ} (lam Lam : ℝ) (a : ParCoeffField d)
    (U : Set (Vec d)) (I : Set ℝ) : Prop where
  measurable : ∀ i j : Fin d, AEMeasurable (fun z => a z i j) (volume.restrict (U ×ˢ I))
  elliptic : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), IsEllipticMatrix lam Lam (a z)

/-- The slice `x ↦ u(x,t)` of a space-time function. -/
def parSlice {d : ℕ} {β : Type*} (u : Vec d × ℝ → β) (t : ℝ) : Vec d → β := fun x => u (x, t)

/-- `L²_c(U)`: `L²` on `U` and vanishing outside a compact subset of `U`. -/
def IsL2c {d : ℕ} (U : Set (Vec d)) (ψ : Vec d → ℝ) : Prop :=
  MemL2On U ψ ∧ ∃ K : Set (Vec d), IsCompact K ∧ K ⊆ U ∧ ∀ x, x ∉ K → ψ x = 0

/-- The parabolic energy space `H¹_par(I × U)` (Definition 5.1), at the level of
every-time representatives: a jointly measurable `u` and spatial gradient in `L²(U ×ˢ I)`
(`MemLp` includes joint a.e.-measurability), slices in `H¹(U)` with weak gradient for a.e. `t`,
every slice in `L²_loc(U)`, and weak continuity of `t ↦ ∫ u(t,·) ψ` on `I` for `ψ ∈ L²_c(U)`. -/
structure ParH1Function {d : ℕ} (U : Set (Vec d)) (I : Set ℝ) where
  toFun : Vec d × ℝ → ℝ
  grad : Vec d × ℝ → Vec d
  memL2 : MemLp toFun 2 (volume.restrict (U ×ˢ I))
  gradMemL2 : ∀ i : Fin d, MemLp (fun z => grad z i) 2 (volume.restrict (U ×ˢ I))
  sliceWeakGradient : ∀ᵐ t ∂(volume.restrict I),
    HasWeakGradientOn U (parSlice toFun t) (parSlice grad t)
  sliceL2loc : ∀ t ∈ I, ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    MemLp (parSlice toFun t) 2 (volume.restrict K)
  weakCont : ∀ ψ : Vec d → ℝ, IsL2c U ψ →
    ContinuousOn (fun t => ∫ x in U, toFun (x, t) * ψ x) I

/-- `C¹` test functions with compact support in the open set `U ×ˢ J`: `C¹_c(J × U)` for open `J`
(used with `J = interior I`). -/
structure ParTestFunction {d : ℕ} (U : Set (Vec d)) (J : Set ℝ) where
  toFun : Vec d × ℝ → ℝ
  contDiff : ContDiff ℝ 1 toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U ×ˢ J

/-- Time derivative `∂ₜφ` of a space-time function (ambient derivative in direction `(0,1)`). -/
noncomputable def parTimeDeriv {d : ℕ} (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  fderiv ℝ φ z (0, 1)

/-- Spatial gradient `∇ₓφ` of a space-time function. -/
noncomputable def parSpaceGrad {d : ℕ} (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : Vec d :=
  fun i => fderiv ℝ φ z (basisVec i, 0)

/-- The integrand `-u ∂ₜφ + a∇u·∇φ` of the weak formulation. -/
noncomputable def parWeakIntegrand {d : ℕ} (a : ParCoeffField d) {U : Set (Vec d)} {I : Set ℝ}
    (u : ParH1Function U I) (φ : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  -(u.toFun z * parTimeDeriv φ z) + vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z)

/-- Weak solution of `∂ₜu - ∇·(a∇u) = 0` in `U × I` (Definition 5.4):
integrability and equality for all `φ ∈ C¹_c(interior I × U)`. -/
def IsParabolicWeakSolution {d : ℕ} (a : ParCoeffField d) (U : Set (Vec d)) (I : Set ℝ)
    (u : ParH1Function U I) : Prop :=
  ∀ φ : ParTestFunction U (interior I),
    IntegrableOn (parWeakIntegrand a u φ.toFun) (U ×ˢ I) ∧
      ∫ z in U ×ˢ I, parWeakIntegrand a u φ.toFun z = 0

/-- `u` is an energy solution of the Cauchy problem on `ℝ^d × [s,T]` with datum `f` at time `s`:
a weak solution in `H¹_par(ℝ^d × [s,T])` whose every-time slice at `s` is `f` a.e. -/
def IsCauchySolution {d : ℕ} (a : ParCoeffField d) (s T : ℝ) (f : Vec d → ℝ)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) : Prop :=
  IsParabolicWeakSolution a univ (Icc s T) u ∧ ∀ᵐ x : Vec d, u.toFun (x, s) = f x

/-! ### The theorem -/

/-- The Nash–Aronson lower bound (Theorem 5.15, kernel-free form, ellipticity constants `1 ≤ Λ`).  For `d > 0`
and `Λ ≥ 1` there are constants `c, β > 0` (depending only on `d` and `Λ`) such that for every parabolic
coefficient field `a` with constants `(1, Λ)` on `ℝ^d × [s, t]`, `s < t`, all `x, y`, all nonnegative
`f, g ∈ L¹ ∩ L²` vanishing almost everywhere outside the balls of radius `√(t - s)/8` about `y` and `x`
respectively, and every energy solution `u` of the Cauchy problem with datum `f` at time `s`,
`c (t - s)^{-d/2} exp (-β |x - y|² / (t - s)) (∫ f)(∫ g) ≤ ∫ g(z) u(z, t) dz`. -/
theorem nashAronsonLower (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (x y : Vec d) (f g : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      (∀ᵐ z : Vec d, 0 ≤ f z) → (∀ᵐ z : Vec d, 0 ≤ g z) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f z = 0) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall x (Real.sqrt (t - s) / 8) → g z = 0) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) *
            ((∫ z, f z) * ∫ z, g z) ≤ ∫ z, g z * u.toFun (z, t) := by
  sorry

end PDE
