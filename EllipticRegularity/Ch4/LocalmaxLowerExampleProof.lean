module

public import EllipticRegularity.Ch4.Examples.Localmax
public import PDEFoundation

/-!
# Proof of `PDE.localmax_lower_example` (Proposition 4.12)

-/

@[expose] public section

namespace PDE.LocalmaxLowerExampleProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ A : Mat d,
        (∀ i j : Fin d, A i j = if i = j then (if i.val + 1 = d then Λ else 1) else 0) ∧
        IsEllipticMatrix 1 Λ A ∧
        ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
          (∀ x : Vec d, u.toFun x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
            Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
              x i ^ 2) / ((d : ℝ) - 1))) ∧
          ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
          (∀ x, 0 < u.toFun x) ∧
          (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
            ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
              (fun i => fderiv ℝ φ x (basisVec i)) ≤ 0) ∧
          essSup (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≥
            ENNReal.ofReal (u.toFun 0) ∧
          ENNReal.ofReal (u.toFun 0) ≥
            ENNReal.ofReal (c * Λ ^ (((d : ℝ) - 1) / 4)) *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  PDE.Ch4Examples.localmax_lower_example_full  d hd

end PDE.LocalmaxLowerExampleProof
