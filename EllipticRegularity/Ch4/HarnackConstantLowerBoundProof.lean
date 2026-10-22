module

public import EllipticRegularity.Ch4.Examples.HarnackConsequences
public import PDEFoundation

/-!
# Proof of `PDE.harnack_constant_lower_bound` (Proposition 4.20)

-/

@[expose] public section

namespace PDE.HarnackConstantLowerBoundProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (CH : ℝ) (hCH : 1 ≤ CH)
    (h : ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ v : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) v (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (v.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal CH *
            essInf (fun x => ENNReal.ofReal (v.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    Real.sqrt Λ ≤ Real.log CH :=
  PDE.Ch4Examples.harnack_constant_lower_bound_full  d hd Λ hΛ CH hCH h

end PDE.HarnackConstantLowerBoundProof
