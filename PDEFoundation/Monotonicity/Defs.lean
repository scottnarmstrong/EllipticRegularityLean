module

public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Chapter 2: definitions for the monotonicity formulas

Surface integrals and means over Euclidean spheres, the Almgren frequency, the first Dirichlet
eigenvalue of a spherical domain and its homogeneity exponent, the Alt--Caffarelli--Friedman
functional, the heat kernel and Poon's parabolic frequency.
Used by the `Ch2Statements` statements.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

noncomputable section

/-- The surface integral `∫_{∂B_r(x)} f dσ` over the Euclidean sphere of radius `r` about `x`.
It is the Mathlib polar-coordinate surface measure `Measure.toSphere` on the unit sphere of the
Euclidean realization `HilbertVec d`, dilated by `r` (surface measure scales by `r ^ (d - 1)`) and
translated by `x`. -/
def sphereIntegral {d : ℕ} (x : Vec d) (r : ℝ) (f : Vec d → ℝ) : ℝ :=
  r ^ (d - 1) *
    ∫ ω : Metric.sphere (0 : HilbertVec d) 1,
      f (x + r • (ω : HilbertVec d).toVec) ∂((volume : Measure (HilbertVec d)).toSphere)

/-- The normalized surface average `⨍_{∂B_r(x)} f`. -/
def sphereMean {d : ℕ} (x : Vec d) (r : ℝ) (f : Vec d → ℝ) : ℝ :=
  ⨍ ω : Metric.sphere (0 : HilbertVec d) 1,
      f (x + r • (ω : HilbertVec d).toVec) ∂((volume : Measure (HilbertVec d)).toSphere)

/-- The Almgren frequency `N_u(r) = r ∫_{B_r} |∇u|² / ∫_{∂B_r} u²` of a classically
differentiable function `u`. -/
def almgrenFrequency {d : ℕ} (u : Vec d → ℝ) (r : ℝ) : ℝ :=
  r * (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x)) /
    sphereIntegral (0 : Vec d) r (fun x => u x ^ 2)

/-- Squared tangential gradient on the unit sphere of the ambient `C¹` function `f`:
`|∇f|² - (∇f · x)²` at `x ∈ ∂B₁`. -/
def tangentialGradientNormSq {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  vecNormSq (classicalGradient f x) - vecDot (classicalGradient f x) x ^ 2

/-- First Dirichlet eigenvalue of `-Δ_{∂B₁}` on `Ω ⊆ ∂B₁`: the infimum of Rayleigh quotients
`∫ |∇_θ f|² / ∫ f²` over `C¹` functions whose support on the sphere is a compact subset of `Ω`
(the infimum over `H¹₀(Ω)` by density).  It is `⊤` exactly when `Ω` is empty. -/
def sphereDirichletEigenvalue (d : ℕ) (Ω : Set (Vec d)) : ℝ≥0∞ :=
  ⨅ (f : Vec d → ℝ)
    (_ : ContDiff ℝ 1 f ∧
      closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆ Ω ∧
      0 < sphereIntegral (0 : Vec d) 1 (fun x => f x ^ 2)),
    ENNReal.ofReal
      (sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq f) /
        sphereIntegral (0 : Vec d) 1 (fun x => f x ^ 2))

/-- The homogeneity exponent `α ∈ [0, ∞]` attached to an eigenvalue `λ ∈ [0, ∞]`:
the largest `α` with `α (α + d - 2) ≤ λ` (`α(α + d - 2) = λ` for finite `λ`; `α = ∞` for `λ = ∞`). -/
def eigenvalueDegree (d : ℕ) (lam : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | a * (a + ((d - 2 : ℕ) : ℝ≥0∞)) ≤ lam}

/-- The Alt--Caffarelli--Friedman functional `r ↦ r⁻⁴ ∏_± ∫_{B_r} |∇u_±|² |x|^{2-d}`, valued
in `[0, ∞]` through lower Lebesgue integrals (no junk value for non-integrable integrands). -/
def acfFunctional {d : ℕ} (Gp Gm : Vec d → Vec d) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (r⁻¹ ^ 4) *
    ((∫⁻ x in euclideanBall (0 : Vec d) r,
        ENNReal.ofReal (vecNormSq (Gp x) / vecEuclideanNorm x ^ (d - 2))) *
      ∫⁻ x in euclideanBall (0 : Vec d) r,
        ENNReal.ofReal (vecNormSq (Gm x) / vecEuclideanNorm x ^ (d - 2)))

/-- The heat kernel `Φ(s,x) = (4π s)^{-d/2} exp(-|x|²/(4s))`. -/
def heatKernel (d : ℕ) (s : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * s))

/-- Poon's `H(s) = ∫ u(-s,x)² Φ(s,x) dx`. -/
def poonH {d : ℕ} (u : ℝ → Vec d → ℝ) (s : ℝ) : ℝ :=
  ∫ x, u (-s) x ^ 2 * heatKernel d s x

/-- Poon's `D(s) = ∫ |∇u(-s,x)|² Φ(s,x) dx`. -/
def poonD {d : ℕ} (u : ℝ → Vec d → ℝ) (s : ℝ) : ℝ :=
  ∫ x, vecNormSq (classicalGradient (u (-s)) x) * heatKernel d s x

/-- Poon's parabolic frequency `𝒩(s) = s D(s) / H(s)`. -/
def poonFrequency {d : ℕ} (u : ℝ → Vec d → ℝ) (s : ℝ) : ℝ :=
  s * poonD u s / poonH u s

end

end PDE
