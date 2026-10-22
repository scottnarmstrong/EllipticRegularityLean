module

public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.BallVolume
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import PDEFoundation.Geometry.C1Boundary
public import PDEFoundation.FunctionalInequalities.Isoperimetric.DimOne
public import PDEFoundation.FunctionalInequalities.Isoperimetric.Minkowski
public import PDEFoundation.FunctionalInequalities.Isoperimetric.Assembly

/-!
# Proof of `PDE.isoperimetric_inequality` (Proposition 1.1)

`PDE.IsoperimetricProof.result` is the isoperimetric inequality
`d |B₁|^{1/d} |E|^{(d-1)/d} ≤ H^{d-1}(∂E)` for bounded nonempty open `E ⊆ ℝᵈ` with `C¹` boundary,
proved by the third argument of the manuscript (Brunn–Minkowski and the Minkowski content):

* `d = 1`: `isoperimetric_dim_one` (`H⁰` is counting measure, `∂E` has two points);
* `d ≥ 2`: `isoperimetric_of_minkowskiBound` (Brunn–Minkowski `PDE.brunn_minkowski` with a closed
  ball, Bernoulli) applied with `minkowski_content_le` (the outer Minkowski content of a `C¹`
  boundary is at most its `μHE[d-1]` measure).
-/

@[expose] public section

namespace PDE.IsoperimetricProof

open MeasureTheory

/-- The Minkowski content bound holds in every dimension. -/
theorem minkowskiBound (d : ℕ) : MinkowskiBound d :=
  fun _E hEo hEb hE hfin _η hη => minkowski_content_le hEo hEb hE hfin hη

/-- The isoperimetric inequality (inequality part of Proposition 1.1). -/
theorem result
    (d : ℕ) (hd : 1 ≤ d) (E : Set (Vec d))
    (hEopen : IsOpen E) (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty)
    (hE : HasC1Boundary E) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) *
        (volume E).toReal ^(((d : ℝ) - 1) / d)) ≤
      (μHE[d - 1] : Measure (HilbertVec d)) (Vec.toHilbertVec '' frontier E) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · exact isoperimetric_dim_one d (by omega) E hEopen hEbdd hEne
  · exact isoperimetric_of_minkowskiBound d h (minkowskiBound d) E hEopen hEbdd hEne hE

end PDE.IsoperimetricProof
