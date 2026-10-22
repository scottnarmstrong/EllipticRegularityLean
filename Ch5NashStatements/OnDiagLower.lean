module

public import EllipticRegularity.Parabolic.Nash.OnDiagLowerProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Proposition 5.12 (mass concentration and `L²` lower bound), `λ = 1`.  `C₁, c` depend on `d` only.
`f = 0` a.e. outside `B_ε(y)` (open Euclidean ball). -/
theorem onDiagLower (d : ℕ) (hd : 0 < d) :
    ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (y : Vec d) (ε : ℝ) (f : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → (∀ᵐ x : Vec d, 0 ≤ f x) → ∫ x, f x = 1 →
      (∀ᵐ x : Vec d, x ∉ euclideanBall y ε → f x = 0) → ε ^ 2 ≤ Lam * (t - s) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        ε ≤ C₁ * Real.sqrt (Lam * (t - s) * Real.log (Real.exp 1 * Lam)) ∧
        (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y
            (C₁ * Real.sqrt (Lam * (t - s) * Real.log (Real.exp 1 * Lam))), u.toFun (x, t) ∧
        ENNReal.ofReal (c * (Lam * Real.log (Real.exp 1 * Lam) * (t - s)) ^ (-(d : ℝ) / 2)) ≤
          ∫⁻ x : Vec d, ENNReal.ofReal (u.toFun (x, t) ^ 2) := by exact PDE.Ch5NashOnDiagLowerProof.result d hd

end PDE
