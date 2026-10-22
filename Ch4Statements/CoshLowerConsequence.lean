module

public import EllipticRegularity.Ch4.CoshLowerConsequenceProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Consequence of Proposition 4.22: if `C` is a constant for which the density estimate
(inequality (4.49) of Proposition 4.11) holds for all `Λ ≥ 1`, `θ ∈ (0,1/2]` and constant
matrices satisfying (4.1), then `C θ^{1/d} Λ^{(d+2)/4} ≥ θ √Λ / C⋆ - log 4` for all
such `Λ`, `θ`. -/
theorem cosh_lower_consequence (d : ℕ) (hd : 3 ≤ d) (Cstar : ℝ)
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
        C * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4) := by exact PDE.CoshLowerConsequenceProof.result d hd Cstar hC C h

end PDE
