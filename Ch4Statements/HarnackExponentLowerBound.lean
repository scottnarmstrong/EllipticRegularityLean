module

public import EllipticRegularity.Ch4.HarnackExponentLowerBoundProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Consequence of Proposition 4.20 for the form `exp(C Λ^β)` of the Harnack constant
(`d ≥ 2`): if for a real `C` (independent of `Λ`) the Harnack inequality holds with constant
`exp(C Λ^β)` for every `Λ ≥ 1`, then `β ≥ 1/2`. -/
theorem harnack_exponent_lower_bound (d : ℕ) (hd : 2 ≤ d) (β C : ℝ)
    (h : ∀ Λ : ℝ, 1 ≤ Λ → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Λ ^ β)) *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    (1 : ℝ) / 2 ≤ β := by exact PDE.HarnackExponentLowerBoundProof.result d hd β C h

end PDE
