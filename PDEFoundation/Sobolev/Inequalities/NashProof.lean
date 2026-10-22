module

public import PDEFoundation.Analysis.Inequalities.Nash.Main
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Proof of `PDE.exists_nash_constant` (Proposition 1.22)

Assembled in `PDE.Nash`.
-/

@[expose] public section

namespace PDE.NashProof

open MeasureTheory

theorem result (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1Function (Set.univ : Set (Vec d)),
      Integrable u.toFun volume →
      ∫ x, u.toFun x ^ 2 ≤
        C * (∫ x, vecEuclideanNorm (u.grad x) ^ 2) ^ ((d : ℝ) / (d + 2)) *
          (∫ x, |u.toFun x|) ^ ((4 : ℝ) / (d + 2)) :=
  PDE.Nash.exists_nash_constant_full d hd

end PDE.NashProof
