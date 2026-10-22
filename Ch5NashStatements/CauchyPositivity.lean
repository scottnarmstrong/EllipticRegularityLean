module

public import EllipticRegularity.Parabolic.Nash.CauchyPositivityProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Positivity of the Cauchy evolution: `f ≥ 0` a.e. gives `u(t) ≥ 0` a.e. for every `t`. -/
theorem cauchyPositivity (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (hu : IsCauchySolution a s T f u)
    (t : ℝ) (ht : t ∈ Icc s T) :
    ∀ᵐ x : Vec d, 0 ≤ u.toFun (x, t) := by exact PDE.Ch5NashCauchyPositivityProof.result d lam Lam a s T hsT ha f hf hf0 u hu t ht

end PDE
