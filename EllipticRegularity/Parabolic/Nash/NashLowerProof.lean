module

public import Ch5NashStatements.LocalHarnack
public import EllipticRegularity.Parabolic.NashLower.Main

/-! # Proof of `PDE.nashAronsonLower` (Theorem 5.15) -/

@[expose] public section

namespace PDE.Ch5NashNashLowerProof

open MeasureTheory Set

/-- The Nash--Aronson lower bound: a chain of parabolic Harnack steps (the proved statement
`PDE.parabLocalHarnack`) started from the on-diagonal lower bound. -/
theorem result (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (x y : Vec d) (f g : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      (∀ᵐ z : Vec d, 0 ≤ f z) → (∀ᵐ z : Vec d, 0 ≤ g z) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f z = 0) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall x (Real.sqrt (t - s) / 8) → g z = 0) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) *
            ((∫ z, f z) * ∫ z, g z) ≤ ∫ z, g z * u.toFun (z, t) :=
  PDE.Ch5NashLowerAssembly.of_localHarnack d hd Lam hLam (PDE.parabLocalHarnack d hd Lam hLam)

end PDE.Ch5NashNashLowerProof
