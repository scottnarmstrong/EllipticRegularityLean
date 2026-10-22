module

public import EllipticRegularity.Parabolic.Nash.NashLowerProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Theorem 5.15, kernel-free (`λ = 1`): `c, β` depend on `(d, Λ)`, chosen after `Λ`, before
all data.  `f`, `g ≥ 0`, supported a.e. in balls of radius `√(t-s)/8` about `y`, `x`. -/
theorem nashAronsonLower (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (x y : Vec d) (f g : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      (∀ᵐ z : Vec d, 0 ≤ f z) → (∀ᵐ z : Vec d, 0 ≤ g z) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f z = 0) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall x (Real.sqrt (t - s) / 8) → g z = 0) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) *
            ((∫ z, f z) * ∫ z, g z) ≤ ∫ z, g z * u.toFun (z, t) := by exact PDE.Ch5NashNashLowerProof.result d hd Lam hLam

end PDE
