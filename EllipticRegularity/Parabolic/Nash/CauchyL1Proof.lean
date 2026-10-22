module

public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction

@[expose] public section

namespace PDE.Ch5NashCauchyL1Proof

open MeasureTheory Set

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧
      eLpNorm (parSlice u.toFun t) 1 volume ≤ eLpNorm f 1 volume := by
  exact PDE.Parabolic.Cauchy.L1.cauchyL1Contraction d lam Lam a s T hsT ha f hf1 hf2 u hu t ht

end PDE.Ch5NashCauchyL1Proof
