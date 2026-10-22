module

public import EllipticRegularity.Ch4.ExpansionSmallProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Expansion of positivity for small `θ` (Proposition 4.15, `d ≥ 3`): there are
`c ∈ (0,1/4]` and `C` such that every nonnegative supersolution `u ∈ H¹(B₁)` with
`|{u ≥ 1} ∩ B₁| ≥ (1-θ)|B₁|`, `θ ∈ (0,c]`, has `essinf_{B_{1/2}} u ≥ exp(-C √Λ)`. -/
theorem expansion_small (d : ℕ) (hd : 3 ≤ d) :
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
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by exact PDE.ExpansionSmallProof.result d hd

end PDE
