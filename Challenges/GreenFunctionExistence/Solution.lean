module

public import EllipticRegularity.Ch4.GreenExistsProof

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory

/-- Existence, uniqueness and basic properties of the Green function (Definition 4.39 and Proposition 4.40),
`d ≥ 3`.  There is `C₀ > 0`, depending only on `d`, such that for all `Λ`, `R > 0` and measurable coefficient
fields `a` on `B_R` with `IsEllipticMatrix 1 Λ (a x)` on `B_R`: a function `G` with `IsGreenFunction a R G`
exists; any two such functions agree almost everywhere on `B_R`; and every such `G` is nonnegative,
satisfies the Stampacchia bounds with constant `C₀` (independent of `Λ` and `R`), has a representative `Gc`
continuous on `B_R \ {0}` which is, away from the pole, an `H¹` weak solution of `-div (a ∇ ·) = 0`, and
satisfies the flux identity `∫_{B_R \ B_ε} ∇φ · a ∇G = φ(0)` for Lipschitz `φ` compactly supported in `B_R`
and constant on `B_ε`. -/
theorem greenExists (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      (∃ G : Vec d → ℝ, IsGreenFunction a R G) ∧
      (∀ G G' : Vec d → ℝ, IsGreenFunction a R G → IsGreenFunction a R G' →
        G =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G') ∧
      ∀ G : Vec d → ℝ, IsGreenFunction a R G →
        (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ G x) ∧
        (IntegrableOn G (euclideanBall (0 : Vec d) R) ∧
          ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) R →
            ∫⁻ x in E, ENNReal.ofReal (G x) ≤
              ENNReal.ofReal (C₀ * (volume E).toReal ^ ((2 : ℝ) / d))) ∧
        (∀ t : ℝ, 0 < t →
          volume {x ∈ euclideanBall (0 : Vec d) R | t < G x} ≤
            ENNReal.ofReal ((C₀ / t) ^ ((d : ℝ) / ((d : ℝ) - 2)))) ∧
        (∃ Gc : Vec d → ℝ,
          ContinuousOn Gc (euclideanBall (0 : Vec d) R \ {0}) ∧
          Gc =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G ∧
          ∀ ε : ℝ, 0 < ε → ε < R →
            ∃ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε),
              H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε)] G ∧
              IsWeakDivergenceFormSolutionOn a
                (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) H
                (0 : Vec d → ℝ) (0 : Vec d → Vec d)) ∧
        (∀ ε : ℝ, 0 < ε → ε < R →
          ∀ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)),
          H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2))] G →
          ∀ φ : Vec d → ℝ, (∃ K : NNReal, LipschitzWith K φ) → HasCompactSupport φ →
            tsupport φ ⊆ euclideanBall (0 : Vec d) R →
            (∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) ε, φ x = c) →
            ∫ x in euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε,
                vecDot (fun i => fderiv ℝ φ x (basisVec i)) (matVecMul (a x) (H.grad x)) = φ 0) :=
  PDE.GreenExistsProof.result d hd

end PDE
