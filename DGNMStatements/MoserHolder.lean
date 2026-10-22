module

public import EllipticRegularity.DeGiorgi.MoserHolderProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Moser's interior Hölder estimate (Theorem 4.21). -/
theorem exists_moser_holder_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, Real.exp (-(C * Real.sqrt Λ)) ≤ α ∧ α ≤ 1 ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ p : ℝ, 1 < p →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤
            ENNReal.ofReal (C * Λ ^ ((d : ℝ) / (2 * p)) * (p / (p - 1)) ^ ((d : ℝ) / p)) *
              eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by exact PDE.MoserHolderProof.result d hd

end PDE
