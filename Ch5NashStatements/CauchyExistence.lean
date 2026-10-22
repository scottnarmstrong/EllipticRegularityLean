module

public import EllipticRegularity.Parabolic.Nash.CauchyExistenceProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Existence for the Cauchy problem (a standard fact used in Section 5.3): every `f ∈ L²(ℝ^d)` has an energy solution on `ℝ^d × [s,T]`. -/
theorem cauchyExistence (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ) (hf : MemLp f 2 volume) :
    ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s T), IsCauchySolution a s T f u := by exact PDE.Ch5NashCauchyExistenceProof.result d lam Lam a s T hsT ha f hf

end PDE
