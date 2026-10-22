module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosedExistence
public import EllipticRegularity.Parabolic.Cauchy.Weights.NashUpperAssembly

/-! # Proof of `PDE.nashAronsonUpper` (Proposition 5.11) -/

@[expose] public section

namespace PDE.Ch5NashNashUpperProof

open MeasureTheory Set

/-- The Nash--Aronson upper estimate, assembled from the two half-interval bounds
and whole-space Cauchy energy solution existence. -/
theorem result (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ r : ℝ, 0 ≤ r → ∀ f g : Vec d → ℝ,
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      ∀ Kf Kg : Set (Vec d), (∀ᵐ x : Vec d, x ∉ Kf → f x = 0) →
        (∀ᵐ x : Vec d, x ∉ Kg → g x = 0) →
        (∀ x ∈ Kf, ∀ y ∈ Kg, r ^ 2 ≤ euclideanSqDist x y) →
        ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t),
          IsCauchySolution a s t f u →
          Integrable (fun x => g x * u.toFun (x, t)) volume ∧
            |∫ x, g x * u.toFun (x, t)| ≤
              C * (t - s) ^ (-(d : ℝ) / 2) *
                Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
                  Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
                ((∫ x, |f x|) * ∫ x, |g x|) := by
  have hExist : ∀ (lam Lam s t : ℝ), s < t →
      ∀ (a : ParCoeffField d), IsParabolicCoeff lam Lam a univ (Icc s t) →
        ∀ f : Vec d → ℝ, MemLp f 2 volume →
          ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s t),
            IsCauchySolution a s t f u := by
    intro lam Lam s t hst a ha f hf
    exact PDE.Parabolic.Lions.exists_cauchy_energy_solution hst ha f hf
  exact PDE.Parabolic.Cauchy.Weights.nashAronsonUpper_of_cauchySolutionExistence
    d hd hExist

end PDE.Ch5NashNashUpperProof
