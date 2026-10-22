module

public import EllipticRegularity.Ch4.Examples.CoshConsequence
public import PDEFoundation

/-!
# Proof of `PDE.cosh_lower_consequence` (Proposition 4.22)

-/

@[expose] public section

namespace PDE.CoshLowerConsequenceProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) (Cstar : ℝ)
    (hC : ENNReal.ofReal Cstar * volume (euclideanBall (0 : Vec d) 1) =
      2 * volume (euclideanBall (0 : Vec (d - 1)) 1))
    (C : ℝ)
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ (Λ : ℝ) (A : Mat d),
      IsEllipticMatrix 1 Λ A →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSuperharmonicOn (fun _ => A) (euclideanBall (0 : Vec d) 1) u →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun x) →
      ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} →
        ENNReal.ofReal (Real.exp (-(C * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4)))) ≤
          essInf (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ Λ : ℝ, 1 ≤ Λ →
      θ * Real.sqrt Λ / Cstar - Real.log 4 ≤
        C * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4) :=
  PDE.Ch4Examples.cosh_lower_consequence_full  d hd Cstar hC C h

end PDE.CoshLowerConsequenceProof
