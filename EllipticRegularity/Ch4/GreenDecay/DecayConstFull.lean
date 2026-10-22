module

public import EllipticRegularity.Ch4.GreenDecay.ConstOsc

/-!
# `greenDecayConst_full`

The exact type of the statement `greenDecayConst` (Corollary 4.37).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

/-- An `H¹₀` solution is unchanged by an almost-everywhere change of the coefficient field. -/
theorem h10Solution_of_coeff_ae_eq {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    {u : H1Function U} {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hab : a =ᵐ[volumeOn U] b) (h : IsWeakDivergenceFormH10SolutionOn a U u f F) :
    IsWeakDivergenceFormH10SolutionOn b U u f F := by
  intro φ
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h φ
  have hpt : (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (matVecMul (b x) (u.grad x)) (φ.toH1Function.grad x) := by
    filter_upwards [hab] with x hx
    rw [hx]
  refine ⟨⟨h1.congr_fun_ae hpt, h2, h3⟩, ?_⟩
  rw [← integral_congr_ae hpt]
  exact h4

/-- Constant coefficients corollary (Corollary 4.37): exact type of the statement
`greenDecayConst`. -/
theorem greenDecayConst_full (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 10 ≤ R → ∀ (a : CoeffField d) (a₀ : Mat d),
      IsEllipticMatrix 1 Λ a₀ →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), a x = a₀) →
      ∀ f : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
        (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) →
      ∀ r : ℝ, 10 ≤ r → r ≤ R →
        eLpMeanNormOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)) 2
            (fun x => u.toH1Function.toFun x -
              integralAverage (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))
                u.toH1Function.toFun) ≤
          ENNReal.ofReal (C * Λ ^ (((d : ℝ) + 4) / 4) * r ^ (1 - (d : ℝ))) *
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨Cs₀, hCs₀, hosc⟩ := osc_of_const hd0
  obtain ⟨C₀, hC₀, hdecay⟩ := greenDecay_full d hd
  refine ⟨C₀ * Cs₀, by positivity, ?_⟩
  intro Λ R hR a a₀ ha₀ hae f hf u hu r hr hrR
  have hΛ1 : 1 ≤ Λ := ha₀.lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hR0 : 0 < R := by linarith
  have hu' : IsWeakDivergenceFormH10SolutionOn (fun _ : Vec d => a₀) (euclideanBall (0 : Vec d) R)
      u.toH1Function (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) :=
    h10Solution_of_coeff_ae_eq hae hu
  have hCs : 0 ≤ Cs₀ * Λ ^ (((d : ℝ) + 2) / 4) := by positivity
  have hAT : IsEllipticMatrix 1 Λ (matTranspose a₀) := isEllipticMatrix_transpose ha₀
  have hosc' : ∀ ρ : ℝ, 4 ≤ ρ → ρ ≤ R → ∀ w : H1Function (euclideanBall (0 : Vec d) ρ),
      IsWeakDivergenceFormSolutionOn (adjointCoeffField (fun _ : Vec d => a₀))
        (euclideanBall (0 : Vec d) ρ) w (0 : Vec d → ℝ) (0 : Vec d → Vec d) →
      ∃ m : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
        m ≤ w.toFun x ∧
        ENNReal.ofReal (w.toFun x - m) ≤
          ENNReal.ofReal ((Cs₀ * Λ ^ (((d : ℝ) + 2) / 4)) * ρ ^ (-(1 : ℝ))) *
            eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
              (fun y => w.toFun y - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun) := by
    intro ρ hρ4 _ w hw
    exact hosc hAT hρ4 w hw
  have key := hdecay Λ R hR (fun _ : Vec d => a₀) (fun i j => aemeasurable_const)
    (fun x _ => ha₀) 1 (Cs₀ * Λ ^ (((d : ℝ) + 2) / 4)) one_pos le_rfl hCs hosc' f hf u hu' r hr hrR
  refine key.trans (le_of_eq ?_)
  congr 2
  rw [show ((d : ℝ) + 4) / 4 = ((d : ℝ) + 2) / 4 + 1 / 2 by ring, Real.rpow_add hΛ0,
    show (2 : ℝ) - 1 - (d : ℝ) = 1 - (d : ℝ) by ring, Real.sqrt_eq_rpow]
  ring

end PDE.Ch4GreenDecay
