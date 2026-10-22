module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The Almgren monotonicity formula

Challenge: monotonicity of the Almgren frequency of a harmonic function, with the equality case.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean dot product, norm and balls are defined below (the norm inherited by `Vec d` from Mathlib
is the supremum norm, and `Metric.ball` is never used).  Spheres carry the Mathlib polar-coordinate
surface measure of the Euclidean realisation `HilbertVec d`.  The frequency is a total real
function: it takes the junk value `0` where the sphere integral of `u²` vanishes.
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


/-- The Euclidean space `ℝ^d` as a `PiLp 2` space, on which Hausdorff measure and sphere measure
are taken. -/
abbrev HilbertVec (d : ℕ) :=
  PiLp 2 (fun _ : Fin d => ℝ)

/-- Put a vector of `Vec d` into `HilbertVec d`. -/
def Vec.toHilbertVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x


/-- Return a vector of `HilbertVec d` to the coordinate carrier `Vec d`. -/
def HilbertVec.toVec {d : ℕ} (x : HilbertVec d) : Vec d :=
  WithLp.ofLp x


/-- The coordinate gradient of a scalar function, expressed in the native vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)


/-- The `i`th classical partial derivative `∂_i u`, computed with `fderiv` on the basis vector. -/
noncomputable def euclideanCoordDeriv {d : ℕ} (i : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ u x (basisVec i)

/-- The classical second partial derivative `∂_j ∂_i u`. -/
noncomputable def euclideanCoordSecondDeriv {d : ℕ} (i j : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ (euclideanCoordDeriv i u) x (basisVec j)

/-- The classical Laplacian `Σ_i ∂_i ∂_i u`. -/
noncomputable def euclideanCoordLaplacian {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, euclideanCoordSecondDeriv i i u x

/-- The surface integral `∫_{∂B_r(x)} f dσ` over the Euclidean sphere of radius `r` about `x`.
It is the Mathlib polar-coordinate surface measure `Measure.toSphere` on the unit sphere of the
Euclidean realization `HilbertVec d`, dilated by `r` (surface measure scales by `r ^ (d - 1)`) and
translated by `x`. -/
noncomputable def sphereIntegral {d : ℕ} (x : Vec d) (r : ℝ) (f : Vec d → ℝ) : ℝ :=
  r ^ (d - 1) *
    ∫ ω : Metric.sphere (0 : HilbertVec d) 1,
      f (x + r • (ω : HilbertVec d).toVec) ∂((volume : Measure (HilbertVec d)).toSphere)

/-- The Almgren frequency `N_u(r) = r ∫_{B_r} |∇u|² / ∫_{∂B_r} u²` of a classically
differentiable function `u`. -/
noncomputable def almgrenFrequency {d : ℕ} (u : Vec d → ℝ) (r : ℝ) : ℝ :=
  r * (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x)) /
    sphereIntegral (0 : Vec d) r (fun x => u x ^ 2)


/-- Almgren frequency monotonicity, with the equality case (Theorem 2.2).  For a harmonic `C²`
function `u` on the ball `B_R`, the frequency `r ↦ r ∫_{B_r} |∇u|² / ∫_{∂B_r} u²` is monotone on
`(0, R)`, and its derivative vanishes at a radius `r` exactly when `u` is a homogeneous polynomial
on `B_R`. -/
theorem almgren_monotonicity (d : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    MonotoneOn (almgrenFrequency u) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R,
        deriv (almgrenFrequency u) r = 0 ↔
          ∃ (k : ℕ) (p : MvPolynomial (Fin d) ℝ), p.IsHomogeneous k ∧
            ∀ x ∈ euclideanBall (0 : Vec d) R, u x = MvPolynomial.eval x p := by
  sorry

end PDE
