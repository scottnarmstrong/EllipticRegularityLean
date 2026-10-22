module

public import EllipticRegularity.Parabolic.Nash.NashUpperProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Proposition 5.11, kernel-free, for any energy solution `u` with datum `f`
(normalization `λ = 1`, so `Λ ≥ 1`).  `C = C(d)` is chosen before `Λ` and all data.
"Supports at distance `≥ r`": sets `Kf, Kg` with `f = 0` a.e. off `Kf`, `g = 0` a.e. off `Kg` and
`r² ≤ |x-y|²` (Euclidean) for `x ∈ Kf`, `y ∈ Kg`.  (Closedness is not needed: closures have the same
separation.) -/
theorem nashAronsonUpper (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ r : ℝ, 0 ≤ r → ∀ f g : Vec d → ℝ,
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      ∀ Kf Kg : Set (Vec d), (∀ᵐ x : Vec d, x ∉ Kf → f x = 0) → (∀ᵐ x : Vec d, x ∉ Kg → g x = 0) →
      (∀ x ∈ Kf, ∀ y ∈ Kg, r ^ 2 ≤ euclideanSqDist x y) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        Integrable (fun x => g x * u.toFun (x, t)) volume ∧
        |∫ x, g x * u.toFun (x, t)| ≤
          C * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
              Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
            ((∫ x, |f x|) * ∫ x, |g x|) := by exact PDE.Ch5NashNashUpperProof.result d hd

end PDE
