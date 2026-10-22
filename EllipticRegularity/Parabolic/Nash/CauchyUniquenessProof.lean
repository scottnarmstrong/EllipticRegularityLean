module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Uniqueness

/-! # Proof of `PDE.cauchyUniqueness` -/

@[expose] public section

namespace PDE.Ch5NashCauchyUniquenessProof

open MeasureTheory Set

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u v : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hv : IsCauchySolution a s T f v) :
    (∀ t ∈ Icc s T, ∀ᵐ x : Vec d, u.toFun (x, t) = v.toFun (x, t)) ∧
      ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)), u.grad z = v.grad z :=
  PDE.Parabolic.Cauchy.Energy.cauchyUniqueness d lam Lam a s T hsT ha f hf u v hu hv

end PDE.Ch5NashCauchyUniquenessProof
