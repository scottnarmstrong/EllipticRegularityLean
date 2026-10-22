module

public import EllipticRegularity.DeGiorgi.WeakHarnackProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The weak Harnack inequality (Proposition 4.17). -/
theorem exists_weakHarnack_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ q : ℝ, 0 < q → q < 1 →
        eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
          ENNReal.ofReal ((C / (1 - q) ^ C) ^ Real.sqrt Λ) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) := by exact PDE.WeakHarnackProof.result d hd

end PDE
