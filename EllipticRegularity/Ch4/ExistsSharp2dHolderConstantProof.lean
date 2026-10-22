module

public import EllipticRegularity.Ch4.Planar.Sharp2d
public import EllipticRegularity.Ch4.Spagnolo.Monotonicity
public import Ch4Statements.WirtingerInequality
public import PDEFoundation

/-!
# Proof of `PDE.exists_sharp2d_holder_constant` (Proposition 4.27)

-/

@[expose] public section

namespace PDE.ExistsSharp2dHolderConstantProof

open MeasureTheory

theorem result :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField 2),
      (∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec 2) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec 2) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u (0 : Vec 2 → ℝ) 0 →
        (∀ x₀ ∈ euclideanBall (0 : Vec 2) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
          ∫ y in euclideanBall x₀ r, vecNormSq (u.grad y) ≤
            Λ * (2 * r) ^ (2 * Λ ^ (-(1 / 2 : ℝ))) *
              ∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y)) ∧
        ∃ (v : Vec 2 → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec 2) (1 / 2))] u.toFun ∧
          0 ≤ M ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec 2) (1 / 2)) v
            (Λ ^ (-(1 / 2 : ℝ))) M ∧
          M ≤ C * Λ * Real.sqrt (∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y)) :=
  PDE.Ch4Planar.exists_sharp2d_holder_constant_full (fun Λ a hm hs he u hsol => PDE.Ch4Spagnolo.piccinini_spagnolo_monotonicity_full (fun w h1 h2 h3 => PDE.wirtinger_inequality w h1 h2 h3) Λ a hm hs he u hsol)

end PDE.ExistsSharp2dHolderConstantProof
