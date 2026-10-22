module

public import EllipticRegularity.Parabolic.Nash.NashKernelProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Kernel form of the Nash--Aronson estimate (5.24).
For fixed `s < t` there is a jointly measurable `P` with `S(t,s) f (x) = ∫ P(x,y) f(y) dy` a.e. for every
`f ∈ L¹∩L²` and every energy solution, and for a.e. `(x,y)` the two-sided Gaussian bounds hold. -/
theorem nashAronsonKernel (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (a : ParCoeffField d) (s t : ℝ), s < t → IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∃ P : Vec d → Vec d → ℝ, Measurable (Function.uncurry P) ∧
        (∀ f : Vec d → ℝ, Integrable f volume → MemLp f 2 volume →
          ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
            ∀ᵐ x : Vec d, Integrable (fun y => P x y * f y) volume ∧
              u.toFun (x, t) = ∫ y, P x y * f y) ∧
        ∀ᵐ p ∂((volume : Measure (Vec d)).prod volume),
          c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist p.1 p.2 / (t - s)) ≤ P p.1 p.2 ∧
          P p.1 p.2 ≤ C * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-euclideanSqDist p.1 p.2 / (8 * Lam * (t - s))) := by exact PDE.Ch5NashNashKernelProof.result d hd

end PDE
