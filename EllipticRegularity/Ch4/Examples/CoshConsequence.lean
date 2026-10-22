module

public import EllipticRegularity.Ch4.Examples.CoshLower

/-!
# Consequence of the `cosh` example (Proposition 4.22)
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

/-- **Consequence of Proposition 4.22**. -/
theorem cosh_lower_consequence_full (d : ℕ) (hd : 3 ≤ d) (Cstar : ℝ)
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
        C * θ ^ ((1 : ℝ) / d) * Λ ^ (((d : ℝ) + 2) / 4) := by
  intro θ hθ hθ' Λ hΛ
  obtain ⟨A, hA, hell, u, hu, hgrad, hsm, hpos, hsol, hdens, hess⟩ :=
    cosh_example_strong d hd Cstar hC Λ hΛ θ hθ hθ'
  have hU : MeasurableSet (euclideanBall (0 : Vec d) 1) := (isOpen_euclideanBall _ _).measurableSet
  have H := h θ hθ hθ' Λ A hell u
    (superharmonic_of_solution (isWeakSolution_of_smooth hU A u hgrad hsm hsol))
    ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx => (hpos x hx).le)) hdens
  have H2 := H.trans hess
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at H2
  have H3 := Real.log_le_log (Real.exp_pos _) H2
  rw [Real.log_exp, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at H3
  linarith

end PDE.Ch4Examples
