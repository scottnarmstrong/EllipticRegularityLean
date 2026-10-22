module

public import EllipticRegularity.Ch4.Planar.Morrey
public import PDEFoundation

/-!
# Proof of `PDE.exists_morrey_growth_constant` (Lemma 4.25)

-/

@[expose] public section

namespace PDE.ExistsMorreyGrowthConstantProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α K : ℝ), 0 < α → α ≤ 1 → 0 ≤ K →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤ K * r ^ ((d : ℝ) - 2 + 2 * α)) →
        ∃ (v : Vec d → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M ∧ EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M ∧
          M ≤ C * α⁻¹ * Real.sqrt K :=
  PDE.Ch4Planar.exists_morrey_growth_constant_full  d hd

end PDE.ExistsMorreyGrowthConstantProof
