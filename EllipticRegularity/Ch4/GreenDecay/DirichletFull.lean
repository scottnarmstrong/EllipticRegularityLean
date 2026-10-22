module

public import EllipticRegularity.Ch4.GreenDecay.DirichletEnergy

/-!
# `greenDirichlet_full`

The exact type of the statement `greenDirichlet` (Lemma 4.33), with
`C₁ = 2` (the Poincaré constant `2R` on `B_R`).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

/-- The coefficient hypotheses pass to the adjoint field. -/
theorem adjoint_coeff_hyps {d : ℕ} {Λ R : ℝ} {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x))
    {b : CoeffField d} (hb : b = a ∨ b = adjointCoeffField a) :
    (∀ i j : Fin d, AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) R))) ∧
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x)) := by
  rcases hb with rfl | rfl
  · exact ⟨hmeas, hell⟩
  · refine ⟨fun i j => ?_, fun x hx => ?_⟩
    · simpa only [adjointCoeffField_apply, matTranspose, Matrix.transpose_apply] using hmeas j i
    · rw [adjointCoeffField_apply]; exact isEllipticMatrix_transpose (hell x hx)

/-- Dirichlet problem (Lemma 4.33): exact type of the statement `greenDirichlet`. -/
theorem greenDirichlet_full (d : ℕ) (hd : 2 ≤ d) :
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
                eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))) := by
  have hd0 : 0 < d := by omega
  refine ⟨2, by norm_num, fun Λ R hR a hmeas hell b hb g F hg hF => ?_⟩
  obtain ⟨hbm, hbell⟩ := adjoint_coeff_hyps hmeas hell hb
  refine ⟨exists_dirichlet_solution hd0 hR hbm hbell hg hF, fun v w hv hw =>
    dirichlet_unique hd0 hR hbm hbell hv hw, ?_⟩
  rintro rfl v hv
  exact dirichlet_energy_bounds hd0 hR hbm hbell hg hv

end PDE.Ch4GreenDecay
