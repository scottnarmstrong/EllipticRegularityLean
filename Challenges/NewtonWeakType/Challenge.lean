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
# Weak-type (1,1) endpoint for the Newtonian potential

Challenge: the gradient of the Newtonian potential `u_F(x) = ∫ E(x - y) · F(y) dy` of a smooth
vector field `F` supported in the unit ball satisfies a local weak-type `(1,1)` estimate on `B₂`,
with constant depending only on the dimension.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, norm and balls are defined below (the norm inherited by `Vec d` from Mathlib
is the supremum norm, and `Metric.ball` is never used).  The kernel `E(z) = z / (d |B₁| |z|^d)` is
the gradient of the fundamental solution of the Laplacian, with the junk value `E 0 = 0`.
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


/-- The coordinate gradient of a scalar function, expressed in the native vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)


/-- The gradient of the fundamental solution of the Laplacian:
`E(z) = z / (d |B₁| |z|^d)`, with `E 0 = 0` (division by zero). -/
noncomputable def newtonKernel {d : ℕ} (z : Vec d) : Vec d :=
  (1 / ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal *
    vecEuclideanNorm z ^ d)) • z

/-- The Newton potential `x ↦ ∫ E(x - y) · F(y) dy` of the field `F`. -/
noncomputable def newtonPotential {d : ℕ} (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y, vecDot (newtonKernel (x - y)) (F y)


/-- Local weak-type `(1,1)` estimate for the gradient of the Newtonian potential `u_F` of a smooth
field `F` supported in `B₁`: there is `C = C(d)` such that
`|{x ∈ B₂ : |∇u_F(x)| > λ}| ≤ C λ⁻¹ ‖F‖_{L¹}` for every `λ > 0`. -/
theorem exists_newtonPotential_weakTypeOne (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) := by
  sorry

end PDE
