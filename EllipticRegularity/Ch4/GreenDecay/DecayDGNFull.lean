module

public import EllipticRegularity.Ch4.GreenDecay.DeGiorgiOsc

/-!
# `greenDecayDGN_full`

The exact type of the statement `greenDecayDGN` (Corollary 4.36).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

/-- Measurable coefficients corollary (Corollary 4.36): exact type of the statement
`greenDecayDGN`. -/
theorem greenDecayDGN_full (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₂ C : ℝ, 0 < C₂ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C₂ * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (R : ℝ), 10 ≤ R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ f : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
        (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) →
      ∀ r : ℝ, 10 ≤ r → r ≤ R →
        eLpMeanNormOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)) 2
            (fun x => u.toH1Function.toFun x -
              integralAverage (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))
                u.toH1Function.toFun) ≤
          ENNReal.ofReal (C * Λ ^ ((1 : ℝ) / 2 + (d : ℝ) / 4) * r ^ (2 - α - (d : ℝ))) *
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨CD, hCD, hDG⟩ := exists_deGiorgi_holder_constant d hd
  obtain ⟨C₀, hC₀, hdecay⟩ := greenDecay_full d (by omega)
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos 0 one_pos
  have hsω : 0 < Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal := Real.sqrt_pos.2 hω
  refine ⟨CD, 4 * C₀ * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD, hCD,
    by positivity, ?_⟩
  intro Λ hΛ
  obtain ⟨α, hα0, hα1, hαexp, hDGa⟩ := hDG Λ hΛ
  refine ⟨α, hα0, hα1, hαexp, ?_⟩
  intro R hR a hmeas hell f hf u hu r hr hrR
  have hΛ0 : 0 < Λ := by linarith
  have hCs : 0 ≤ 4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
      Λ ^ ((d : ℝ) / 4) := by positivity
  obtain ⟨hbmT, hbellT⟩ := adjoint_coeff_hyps hmeas hell
    (Or.inr rfl : adjointCoeffField a = a ∨ adjointCoeffField a = adjointCoeffField a)
  have hosc : ∀ ρ : ℝ, 4 ≤ ρ → ρ ≤ R → ∀ w : H1Function (euclideanBall (0 : Vec d) ρ),
      IsWeakDivergenceFormSolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) ρ) w
        (0 : Vec d → ℝ) (0 : Vec d → Vec d) →
      ∃ m : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
        m ≤ w.toFun x ∧
        ENNReal.ofReal (w.toFun x - m) ≤
          ENNReal.ofReal ((4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
              Λ ^ ((d : ℝ) / 4)) * ρ ^ (-α)) *
            eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
              (fun y => w.toFun y - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun) := by
    intro ρ hρ4 hρR w hw
    have hsub : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) R :=
      euclideanBall_mono (by linarith) hρR
    exact osc_of_deGiorgi hCD hΛ hα0 hα1 hDGa hρ4
      (fun i j => (hbmT i j).mono_measure (Measure.restrict_mono hsub le_rfl))
      (fun x hx => hbellT x (hsub hx)) w hw
  have key := hdecay Λ R hR a hmeas hell α
    (4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD * Λ ^ ((d : ℝ) / 4))
    hα0 hα1 hCs hosc f hf u hu r hr hrR
  have heq : C₀ * (4 * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
        Λ ^ ((d : ℝ) / 4)) * Real.sqrt Λ * r ^ (2 - α - (d : ℝ)) =
      4 * C₀ * Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * CD *
        Λ ^ ((1 : ℝ) / 2 + (d : ℝ) / 4) * r ^ (2 - α - (d : ℝ)) := by
    rw [Real.rpow_add hΛ0]
    simp only [Real.sqrt_eq_rpow]
    ring
  refine key.trans (le_of_eq ?_)
  rw [heq]

end PDE.Ch4GreenDecay
