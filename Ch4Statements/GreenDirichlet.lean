module

public import EllipticRegularity.Ch4.GreenDirichletProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Dirichlet problem (Lemma 4.33): for `b ∈ {a, aᵗ}`, `g ∈ L²(B_R)`,
`F ∈ L²(B_R;ℝᵈ)`, existence and a.e. uniqueness of the `H¹₀(B_R)` solution of
`-div (b ∇ v) = g + div F`, and the energy bounds when `F = 0`. -/
theorem greenDirichlet (d : ℕ) (hd : 2 ≤ d) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ b : CoeffField d, (b = a ∨ b = adjointCoeffField a) →
      ∀ (g : Vec d → ℝ) (F : Vec d → Vec d),
        MemL2On (euclideanBall (0 : Vec d) R) g →
        MemVectorL2On (euclideanBall (0 : Vec d) R) F →
        (∃ v : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F) ∧
        (∀ v w : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F →
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) w.toH1Function g F →
            v.toH1Function.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] w.toH1Function.toFun ∧
            v.toH1Function.grad =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] w.toH1Function.grad) ∧
        (F = (0 : Vec d → Vec d) →
          ∀ v : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F →
            eLpNorm (fun x => vecEuclideanNorm (v.toH1Function.grad x)) 2
                (volumeOn (euclideanBall (0 : Vec d) R)) ≤
              ENNReal.ofReal (C₁ * R) * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) ∧
            eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≤
              ENNReal.ofReal (C₁ ^ 2 * R ^ 2) *
                eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))) := by exact PDE.GreenDirichletProof.result d hd

end PDE
