module

public import EllipticRegularity.Ch4.ExistsMorreyGrowthConstantProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Morrey's Dirichlet growth theorem (Lemma 4.25), all `d ≥ 2`.
If `∫_{B_r(x)} |∇u|² ≤ K r^{d-2+2α}` for `x ∈ B_{1/2}`, `r ∈ (0,1/2]`, then `u` has a
representative Hölder on `B_{1/2}` with seminorm at most `C α⁻¹ K^{1/2}`. -/
theorem exists_morrey_growth_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α K : ℝ), 0 < α → α ≤ 1 → 0 ≤ K →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤ K * r ^ ((d : ℝ) - 2 + 2 * α)) →
        ∃ (v : Vec d → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M ∧ EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M ∧
          M ≤ C * α⁻¹ * Real.sqrt K := by exact PDE.ExistsMorreyGrowthConstantProof.result d hd

end PDE
