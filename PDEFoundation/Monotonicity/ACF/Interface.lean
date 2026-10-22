module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.H1.Basic

/-!
# Alt--Caffarelli--Friedman: shared slice quantities

Definitions shared by the Alt--Caffarelli--Friedman modules (weighted bound, slice Rayleigh bound, assembly).  All
radial-slice quantities of an `H¹` function are expressed through the sphere integral
`PDE.sphereIntegral 0 r` applied to functions of `x` built from `u.toFun` and `u.grad`; no trace
operator is used.  For a point `x` on `∂B_r` the quantity `radialDeriv u.grad x` is the radial
derivative `∂_r u`.

* `acfWeightedEnergy G r = ∫⁻_{B_r} ofReal(|G|² / |x|^{d-2})`, the factor appearing in
  `acfFunctional`.
* `acfSliceMass u r = a(r)`, `acfSliceRadial G r = b(r)`, `acfSliceGrad G r = c(r)`,
  `acfSliceFlux u G r = ∫_{∂B_r} u (x · G)`: the slice quantities, all defined by `sphereIntegral 0 r`.
* `SphereIntegrable r f`: the slice `ω ↦ f (r ω)` is integrable for the surface measure, so that
  `sphereIntegral 0 r f` is not a junk value.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

noncomputable section

/-- Radial derivative `x · G(x) / |x|` of a gradient field `G`. -/
def radialDeriv {d : ℕ} (G : Vec d → Vec d) (x : Vec d) : ℝ :=
  vecDot x (G x) / vecEuclideanNorm x

/-- The slice of `f` over the sphere of radius `r` (about `0`) is integrable for the surface
measure used in `sphereIntegral`. -/
def SphereIntegrable {d : ℕ} (r : ℝ) (f : Vec d → ℝ) : Prop :=
  Integrable (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
    f ((0 : Vec d) + r • (ω : HilbertVec d).toVec))
    ((volume : Measure (HilbertVec d)).toSphere)

/-- The weighted energy `∫⁻_{B_r} ofReal (|G|² / |x|^{d-2})`: exactly the factor of
`acfFunctional`. -/
def acfWeightedEnergy {d : ℕ} (G : Vec d → Vec d) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in euclideanBall (0 : Vec d) r,
    ENNReal.ofReal (vecNormSq (G x) / vecEuclideanNorm x ^ (d - 2))

/-- `a(r) = ∫_{∂B_r} u²`. -/
def acfSliceMass {d : ℕ} (u : Vec d → ℝ) (r : ℝ) : ℝ :=
  sphereIntegral (0 : Vec d) r (fun x => u x ^ 2)

/-- `b(r) = ∫_{∂B_r} (∂_r u)²`. -/
def acfSliceRadial {d : ℕ} (G : Vec d → Vec d) (r : ℝ) : ℝ :=
  sphereIntegral (0 : Vec d) r (fun x => radialDeriv G x ^ 2)

/-- `c(r) = ∫_{∂B_r} |∇u|²`. -/
def acfSliceGrad {d : ℕ} (G : Vec d → Vec d) (r : ℝ) : ℝ :=
  sphereIntegral (0 : Vec d) r (fun x => vecNormSq (G x))

/-- The radial flux `∫_{∂B_r} u (x · ∇u) = r ∫_{∂B_r} u ∂_r u`. -/
def acfSliceFlux {d : ℕ} (u : Vec d → ℝ) (G : Vec d → Vec d) (r : ℝ) : ℝ :=
  sphereIntegral (0 : Vec d) r (fun x => u x * vecDot x (G x))

theorem acfFunctional_eq_mul {d : ℕ} (Gp Gm : Vec d → Vec d) (r : ℝ) :
    acfFunctional Gp Gm r =
      ENNReal.ofReal (r⁻¹ ^ 4) * (acfWeightedEnergy Gp r * acfWeightedEnergy Gm r) :=
  rfl

end

end PDE
