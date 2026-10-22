module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Positivity

/-! # Proof of `PDE.cauchyPositivity` -/

@[expose] public section

namespace PDE.Ch5NashCauchyPositivityProof

open MeasureTheory Set

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    ∀ᵐ x : Vec d, 0 ≤ u.toFun (x, t) :=
  PDE.Parabolic.Cauchy.Energy.cauchyPositivity d lam Lam a s T hsT ha f hf hf0 u hu t ht

end PDE.Ch5NashCauchyPositivityProof
