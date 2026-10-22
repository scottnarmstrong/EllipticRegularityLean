module

public import EllipticRegularity.Parabolic.CauchyDef
public import EllipticRegularity.Parabolic.Cauchy.Duality.AdjCoeff

@[expose] public section

open MeasureTheory Set

/-!
# Proof of `PDE.parAdjCoeff_isParabolicCoeff`
-/

namespace PDE.Ch5NashCauchyAdjCoeffProof

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) :
    IsParabolicCoeff lam Lam (parAdjCoeff a (s + T)) univ (Icc s T) :=
  PDE.parAdjCoeff_isParabolicCoeff_core d lam Lam a s T ha

end PDE.Ch5NashCauchyAdjCoeffProof
