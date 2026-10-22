module

public import PDEFoundation.Analysis.Gehring.LocalItFinal
public import PDEFoundation.Analysis.Gehring.Global

/-!
# The quantitative Gehring lemma (Lemma 4.6), root theorem

`exists_gehring_constant_full` is a theorem whose type is, verbatim, that of
`PDE.exists_gehring_constant`. The constant is
`C = max (gehringGlobalC d) (gehringLocalC d)`, chosen before `σ, A, B, ε, g, h`.
-/

@[expose] public section

namespace PDE.GehringFull

open MeasureTheory
open PDE.Gehring

/-- The quantitative Gehring lemma (Lemma 4.6), global and local
versions. The constant `C` plays the role of `C₁(d)`. -/
theorem exists_gehring_constant_full
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
                  (ENNReal.ofReal (1 + ε)) h) := by
  refine ⟨max (gehringGlobalC d) (gehringLocalC d),
    le_max_of_le_left (one_le_gehringGlobalC d), ?_⟩
  intro σ hσ A B ε hA hB hε hεA g h hg0 hh0
  have hCg : gehringGlobalC d ≤ max (gehringGlobalC d) (gehringLocalC d) := le_max_left _ _
  have hCl : gehringLocalC d ≤ max (gehringGlobalC d) (gehringLocalC d) := le_max_right _ _
  have hA0 : 0 < A := by linarith
  have hεg : ε ≤ 1 / (gehringGlobalC d * A) :=
    hεA.trans (one_div_le_one_div_of_le (by have := one_le_gehringGlobalC d; positivity)
      (mul_le_mul_of_nonneg_right hCg hA0.le))
  have hG := gehringG_pos d
  have h8 := eight_mul_G_le_globalC d
  have hεl : ε ≤ 1 / (8 * gehringG d * A) :=
    hεg.trans (one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right h8 hA0.le))
  constructor
  · rintro ⟨hg, hc, hh, hrh⟩
    have := gehring_global hd hσ hA hB hε hεg hg0 hh0 hg hc hh hrh
    exact this.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCg hB)) _)
  · rintro ⟨hgI, hhM, hrh⟩
    have := gehring_local hd hσ hA hB hε hεl hg0 hh0 hgI hhM hrh
    have hav : 0 ≤ integralAverage (euclideanBall (0 : Vec d) 1) g :=
      integralAverage_nonneg (isOpen_euclideanBall _ _).measurableSet fun x _ => hg0 x
    refine this.trans (add_le_add (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCl hav)) (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCl hB)) _))

end PDE.GehringFull
