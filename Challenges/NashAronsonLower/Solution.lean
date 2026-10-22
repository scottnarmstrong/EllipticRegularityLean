module

public import EllipticRegularity.Parabolic.Nash.NashLowerProof

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory Set

/-- The Nash–Aronson lower bound (Theorem 5.15, kernel-free form, ellipticity constants `1 ≤ Λ`).  For `d > 0`
and `Λ ≥ 1` there are constants `c, β > 0` (depending only on `d` and `Λ`) such that for every parabolic
coefficient field `a` with constants `(1, Λ)` on `ℝ^d × [s, t]`, `s < t`, all `x, y`, all nonnegative
`f, g ∈ L¹ ∩ L²` vanishing almost everywhere outside the balls of radius `√(t - s)/8` about `y` and `x`
respectively, and every energy solution `u` of the Cauchy problem with datum `f` at time `s`,
`c (t - s)^{-d/2} exp (-β |x - y|² / (t - s)) (∫ f)(∫ g) ≤ ∫ g(z) u(z, t) dz`. -/
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
            ((∫ z, f z) * ∫ z, g z) ≤ ∫ z, g z * u.toFun (z, t) :=
  PDE.Ch5NashNashLowerProof.result d hd Lam hLam

end PDE
