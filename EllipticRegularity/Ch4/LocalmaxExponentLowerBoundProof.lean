module

public import EllipticRegularity.Ch4.Examples.Localmax
public import PDEFoundation

/-!
# Proof of `PDE.localmax_exponent_lower_bound` (Proposition 4.12)

-/

@[expose] public section

namespace PDE.LocalmaxExponentLowerBoundProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) (γ C : ℝ)
    (h : ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ γ) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))) :
    ((d : ℝ) - 1) / 4 ≤ γ :=
  PDE.Ch4Examples.localmax_exponent_lower_bound_full  d hd γ C h

end PDE.LocalmaxExponentLowerBoundProof
