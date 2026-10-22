module

public import PDEFoundation.Sobolev.Inequalities.BombieriProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Bombieri lemma (Lemma 1.13). -/
theorem exists_bombieri_bound (d : ℕ) (hd : 1 ≤ d) (q k A : ℝ) (hq : 0 < q) (hk : 0 < k)
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
        ENNReal.ofReal C := by exact PDE.BombieriProof.result d hd q k A hq hk hA

end PDE
