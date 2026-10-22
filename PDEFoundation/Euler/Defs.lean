module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Weak solutions of the 2d Euler equations on the unit torus

Definitions for Proposition 3.12: the torus `𝕋² = ℝ²/ℤ²` as
`ℤ²`-periodic functions on `Vec 2` integrated over the unit cube, weak solutions with an initial datum,
bounded vorticity, and the energy inequality.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE


/-- The unit cube, fundamental domain of `𝕋² = ℝ²/ℤ²`. -/
def torusCube : Set (Vec 2) := Set.Icc (0 : Vec 2) 1

/-- Pointwise `ℤ²`-periodicity of a function on `ℝ²`. -/
def IsTorusPeriodic {β : Type*} (f : Vec 2 → β) : Prop :=
  ∀ (i : Fin 2) (x : Vec 2), f (x + basisVec i) = f x

/-- Space-time measure on `𝕋² × [0,T]`, space first: Lebesgue on `[0,1]² × [0,T]`. -/
noncomputable def eulerMeasure (T : ℝ) : Measure (Vec 2 × ℝ) :=
  volume.restrict (torusCube ×ˢ Icc 0 T)

/-- Time derivative of a vector field on space-time. -/
noncomputable def eulerTimeDeriv (φ : Vec 2 × ℝ → Vec 2) (z : Vec 2 × ℝ) : Vec 2 :=
  fun i => fderiv ℝ (fun w => φ w i) z (0, 1)

/-- `∂_j φ_i`. -/
noncomputable def eulerSpaceDeriv (φ : Vec 2 × ℝ → Vec 2) (z : Vec 2 × ℝ) (i j : Fin 2) : ℝ :=
  fderiv ℝ (fun w => φ w i) z (basisVec j, 0)

/-- Spatial divergence. -/
noncomputable def eulerDiv (φ : Vec 2 × ℝ → Vec 2) (z : Vec 2 × ℝ) : ℝ :=
  ∑ i, eulerSpaceDeriv φ z i i

/-- Smooth space-periodic space-time vector field. -/
def IsPeriodicSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Vec 2 × ℝ → E) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ ∀ t, IsTorusPeriodic (fun x => φ (x, t))

/-- `C_c^∞((0,T) × 𝕋²)`-class (time support compact in `(0,T)`). -/
def VanishesOutsideInterior {E : Type*} [Zero E] (T : ℝ) (φ : Vec 2 × ℝ → E) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ b < T ∧ ∀ x t, t ∉ Icc a b → φ (x, t) = 0

/-- `C_c^∞([0,T) × 𝕋²)`-class (vanishes for `t ≥ b`, some `b < T`). -/
def VanishesNearTerminal {E : Type*} [Zero E] (T : ℝ) (φ : Vec 2 × ℝ → E) : Prop :=
  ∃ b : ℝ, b < T ∧ ∀ x t, b ≤ t → φ (x, t) = 0

/-- Weak-formulation integrand `v·∂_tφ + (v⊗v):∇φ`. -/
noncomputable def eulerWeakIntegrand (v φ : Vec 2 × ℝ → Vec 2) (z : Vec 2 × ℝ) : ℝ :=
  vecDot (v z) (eulerTimeDeriv φ z) + ∑ i, ∑ j, v z i * v z j * eulerSpaceDeriv φ z i j

/-- Weak solution of Euler on `[0,T] × 𝕋²` as in the manuscript. -/
def IsEulerWeakSolution (T : ℝ) (v : Vec 2 × ℝ → Vec 2) : Prop :=
  AEStronglyMeasurable v (eulerMeasure T) ∧
  (∀ t, IsTorusPeriodic (fun x => v (x, t))) ∧
  (∃ B : ℝ, ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      ∫⁻ x in torusCube, ENNReal.ofReal (vecNormSq (v (x, t))) ≤ ENNReal.ofReal B) ∧
  (∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, vecDot (v z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0) ∧
  (∀ φ : Vec 2 × ℝ → Vec 2, IsPeriodicSmooth φ → VanishesOutsideInterior T φ →
      (∀ z, eulerDiv φ z = 0) →
      ∫ z, eulerWeakIntegrand v φ z ∂(eulerMeasure T) = 0)

/-- Weak solution attaining the initial datum `v₀` in the weak sense; the datum is an `L²`
distributionally divergence-free field. -/
def IsEulerWeakSolutionWithDatum (T : ℝ) (v₀ : Vec 2 → Vec 2) (v : Vec 2 × ℝ → Vec 2) : Prop :=
  IsEulerWeakSolution T v ∧
  MemLp v₀ 2 (volume.restrict torusCube) ∧
  (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, vecDot (v₀ x) (fun j => fderiv ℝ ψ x (basisVec j)) = 0) ∧
  (∀ φ : Vec 2 × ℝ → Vec 2, IsPeriodicSmooth φ → VanishesNearTerminal T φ →
      (∀ z, eulerDiv φ z = 0) →
      ∫ z, eulerWeakIntegrand v φ z ∂(eulerMeasure T)
        + ∫ x in torusCube, vecDot (v₀ x) (φ (x, 0)) = 0)

/-- `ω = ∂₁v₂ - ∂₂v₁` (distributionally, in space-time) is an `L^∞` function bounded by `M`. -/
def HasBoundedVorticity (T M : ℝ) (v : Vec 2 × ℝ → Vec 2) : Prop :=
  ∃ ω : Vec 2 × ℝ → ℝ, AEStronglyMeasurable ω (eulerMeasure T) ∧
    (∀ᵐ z ∂(eulerMeasure T), |ω z| ≤ M) ∧
    ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, ω z * ψ z ∂(eulerMeasure T) =
        ∫ z, (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) - v z 1 * fderiv ℝ ψ z (basisVec 0, 0))
          ∂(eulerMeasure T)

/-- Energy inequality `‖v(t)‖₂ ≤ ‖v₀‖₂` for a.e. `t ∈ [0,T]`. -/
def HasEnergyInequality (T : ℝ) (v₀ : Vec 2 → Vec 2) (v : Vec 2 × ℝ → Vec 2) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
    ∫⁻ x in torusCube, ENNReal.ofReal (vecNormSq (v (x, t)))
      ≤ ∫⁻ x in torusCube, ENNReal.ofReal (vecNormSq (v₀ x))

end PDE
