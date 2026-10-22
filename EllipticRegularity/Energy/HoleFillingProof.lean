module

public import EllipticRegularity.Energy.CubeHoleFillingConclusion
public import PDEFoundation.PDE.CoefficientModification

/-!
# Proof of `PDE.exists_holeFilling_constant` (Lemma 4.2)

The sharp hole-filling estimate for coefficients whose entries are
a.e. measurable and which are elliptic at every point of the unit ball.
A measurable elliptic representative of the coefficients carries the same
weak solution, and the cube hole-filling theorem applies to it.
-/

@[expose] public section

namespace PDE.HoleFillingProof

open MeasureTheory

theorem result
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
          (0 : Vec d → ℝ) (0 : Vec d → Vec d) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        Real.sqrt (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (u.grad x)) ≤
          C * Real.sqrt Λ * r ^ ((C * Λ) ^ (-(1 / 2 : ℝ))) *
            Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, u.toFun x ^ 2) := by
  refine ⟨cubeHoleFillingConst d, cubeHoleFillingConst_pos hd, ?_⟩
  intro Λ a ha hEll u hsol r hr hrhalf
  obtain ⟨b, hbEll, -, hbsol⟩ :=
    exists_isEllipticFieldOn_and_weakSolutionOn_coeffAEEqOn
      (measurableSet_euclideanBall (0 : Vec d) 1) ha hEll hsol
  exact holeFilling_of_isEllipticFieldOn hd hbEll hbsol hr hrhalf

end PDE.HoleFillingProof
