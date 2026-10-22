module

public import EllipticRegularity.Parabolic.Nash.CauchyMassProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Mass conservation for `f ∈ L¹ ∩ L²`: `u(t) ∈ L¹` and `∫ u(t) = ∫ f`. -/
theorem cauchyMass (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (hu : IsCauchySolution a s T f u)
    (t : ℝ) (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧ ∫ x, u.toFun (x, t) = ∫ x, f x := by exact PDE.Ch5NashCauchyMassProof.result d lam Lam a s T hsT ha f hf1 hf2 u hu t ht

end PDE
