module

public import EllipticRegularity.Ch4.LocalmaxExponentLowerBoundProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Exponent consequence of Proposition 4.12 (d ≥ 3): if
`esssup_{B_{1/2}} u_+ ≤ C Λ^γ ‖u‖_{L²(B₁)}` for every `Λ ≥ 1`, every `a` satisfying (4.1)
and every subsolution `u ∈ H¹(B₁)`, then `γ ≥ (d-1)/4`. -/
theorem localmax_exponent_lower_bound (d : ℕ) (hd : 3 ≤ d) (γ C : ℝ)
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
    ((d : ℝ) - 1) / 4 ≤ γ := by exact PDE.LocalmaxExponentLowerBoundProof.result d hd γ C h

end PDE
