module

public import EllipticRegularity.Parabolic.CauchyDef
public import EllipticRegularity.Parabolic.Cauchy.Duality.MassGeneral

/-!
# Proof of `PDE.cauchyMass`
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Ch5NashCauchyMassProof

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧
      ∫ x, u.toFun (x, t) = ∫ x, f x :=
  PDE.Parabolic.Duality.cauchy_mass_l1_l2_core d lam Lam a s T hsT ha f hf1 hf2 u hu t ht

end PDE.Ch5NashCauchyMassProof
