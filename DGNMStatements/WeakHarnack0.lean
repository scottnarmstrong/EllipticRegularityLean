module

public import EllipticRegularity.DeGiorgi.WeakHarnack0Proof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The weak Harnack estimates (Proposition 4.14). -/
theorem exists_weakHarnack0_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ p : ℝ, 0 < p →
        ENNReal.ofReal ((Λ * p ^ 2 + 1) ^ (-((d : ℝ) / 2))) *
            (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x)⁻¹ ^ p) ∂volume)⁻¹ ≤
          ENNReal.ofReal C *
            (essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p) ∧
      (∀ p q : ℝ, 0 < p → p ≤ q → q < 1 →
        (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p ∧
        ∀ m : ℕ, 1 ≤ m → p = q * ((d : ℝ) / (d - 2)) ^ (-(m : ℝ)) →
          (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
            ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) *
              (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p) := by exact PDE.WeakHarnack0Proof.result d hd

end PDE
