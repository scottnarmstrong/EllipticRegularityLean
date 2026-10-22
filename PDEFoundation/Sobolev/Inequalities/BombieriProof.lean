module

public import PDEFoundation.Analysis.Inequalities.Bombieri.Full
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Proof of `PDE.exists_bombieri_bound` (Lemma 1.13)

Assembled in `PDE.Bombieri` from the Bombieri--Giusti iteration.
-/

@[expose] public section

namespace PDE.BombieriProof

open MeasureTheory

theorem result (d : ℕ) (hd : 1 ≤ d) (q k A : ℝ) (hq : 0 < q) (hk : 0 < k)
    (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Vec d → ℝ,
      MemLp v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v x) →
      eLpNorm (fun x => Real.log (v x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
        ENNReal.ofReal A →
      (∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ min 1 (q / 2) →
        eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) r)) ≤
          ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / p)) *
            eLpMeanNormOn (euclideanBall (0 : Vec d) s) (ENNReal.ofReal p) v) →
      eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        ENNReal.ofReal C :=
  PDE.Bombieri.exists_bombieri_bound_full d hd q k A hq hk hA

end PDE.BombieriProof
