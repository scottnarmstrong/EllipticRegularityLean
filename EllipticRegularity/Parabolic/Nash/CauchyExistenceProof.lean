module

public import EllipticRegularity.Parabolic.CauchyDef
public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosedExistence

/-! # Proof of `PDE.cauchyExistence` -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Ch5NashCauchyExistenceProof

/-- The whole-space parabolic Cauchy existence theorem, supplied by the Lions construction. -/
theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume) :
    ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s T), IsCauchySolution a s T f u := by
  exact PDE.Parabolic.Lions.exists_cauchy_energy_solution hsT ha f hf

end PDE.Ch5NashCauchyExistenceProof
