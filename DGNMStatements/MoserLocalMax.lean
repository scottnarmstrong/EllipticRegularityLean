module

public import EllipticRegularity.DeGiorgi.MoserLocalMaxProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Moser's L^∞ estimate for subsolutions (Proposition 4.13). -/
theorem exists_moserLocalMax_constant (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ p : ℝ, 1 < p →
        (essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p := by exact PDE.MoserLocalMaxProof.result d hd

end PDE
