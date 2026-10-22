module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Full
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Proof of `PDE.exists_johnNirenberg_constant` (Proposition 1.17)

Assembled in `PDE.JohnNirenberg` (cubes) and `PDE.JohnNirenbergBall` (balls).
-/

@[expose] public section

namespace PDE.JohnNirenbergProof

open MeasureTheory

theorem result (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec d) (R : ℝ), 0 < R → ∀ (u : Vec d → ℝ) (M : ℝ), 0 < M →
      LocallyIntegrableOn u (euclideanBall x R) volume →
      (∀ (y : Vec d) (r : ℝ), 0 < r → closure (euclideanBall y r) ⊆ euclideanBall x R →
        integralAverage (euclideanBall y r) (fun z => |u z - integralAverage (euclideanBall y r) u|) ≤ M) →
      IntegrableOn u (euclideanBall x R) volume ∧
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ euclideanBall x R | t < |u z - integralAverage (euclideanBall x R) u|}).toReal ≤
          C * Real.exp (-(t / (C * M))) * (volume (euclideanBall x R)).toReal :=
  PDE.JohnNirenbergBall.exists_johnNirenberg_constant_full d hd

end PDE.JohnNirenbergProof
