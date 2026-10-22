module

public import EllipticRegularity.Ch4.Examples.Expansion
public import PDEFoundation

/-!
# Proof of `PDE.expansion_small` (Proposition 4.15)

-/

@[expose] public section

namespace PDE.ExpansionSmallProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ θ : ℝ, 0 < θ → θ ≤ c →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 ≤ u.toFun x) →
      ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
        volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} →
        ENNReal.ofReal (Real.exp (-(C * Real.sqrt Λ))) ≤
          essInf (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) :=
  PDE.Ch4Examples.expansion_small_full  d hd

end PDE.ExpansionSmallProof
