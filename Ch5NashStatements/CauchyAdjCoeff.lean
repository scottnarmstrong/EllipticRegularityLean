module

public import EllipticRegularity.Parabolic.Nash.CauchyAdjCoeffProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Time reversal plus transposition preserves (5.1) on `ℝ^d × [s,T]`. -/
theorem parAdjCoeff_isParabolicCoeff (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) :
    IsParabolicCoeff lam Lam (parAdjCoeff a (s + T)) univ (Icc s T) := by exact PDE.Ch5NashCauchyAdjCoeffProof.result d lam Lam a s T ha

end PDE
