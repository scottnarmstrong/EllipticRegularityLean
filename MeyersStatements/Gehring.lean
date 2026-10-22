module

public import PDEFoundation.Analysis.GehringProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The quantitative Gehring lemma (Lemma 4.6), global and local
versions. The constant `C` plays the role of `C₁(d)`. -/
theorem exists_gehring_constant
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (σ : ℝ), (σ = 2 ∨ σ = 4) →
      ∀ (A B ε : ℝ), 1 ≤ A → 0 ≤ B → 0 < ε → ε ≤ 1 / (C * A) →
      ∀ g h : Vec d → ℝ, (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
        ((Integrable g volume ∧ HasCompactSupport g ∧
            MemLp h (ENNReal.ofReal (1 + ε)) volume ∧
            ∀ (z : Vec d) (r : ℝ), 0 < r →
              ∫ x in centeredAxisCube z r, g x ≤
                A * (volume (centeredAxisCube z r)).toReal *
                    (integralAverage (centeredAxisCube z (σ * r))
                      (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
                        (((d : ℝ) + 1) / (d : ℝ)) +
                  B * ∫ x in centeredAxisCube z (σ * r), h x) →
          eLpNorm g (ENNReal.ofReal (1 + ε)) volume ≤
            ENNReal.ofReal (C * B) *
              eLpNorm h (ENNReal.ofReal (1 + ε)) volume) ∧
        ((IntegrableOn g (euclideanBall (0 : Vec d) 1) volume ∧
            MemLp h (ENNReal.ofReal (1 + ε))
              (volumeOn (euclideanBall (0 : Vec d) 1)) ∧
            ∀ (z : Vec d) (r : ℝ), 0 < r →
              centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) 1 →
              ∫ x in centeredAxisCube z r, g x ≤
                A * (volume (centeredAxisCube z r)).toReal *
                    (integralAverage (centeredAxisCube z (σ * r))
                      (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
                        (((d : ℝ) + 1) / (d : ℝ)) +
                  B * ∫ x in centeredAxisCube z (σ * r), h x) →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2))
              (ENNReal.ofReal (1 + ε)) g ≤
            ENNReal.ofReal (C * integralAverage (euclideanBall (0 : Vec d) 1) g) +
              ENNReal.ofReal (C * B) *
                eLpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal (1 + ε)) h) := by exact PDE.GehringProof.result d hd

end PDE
