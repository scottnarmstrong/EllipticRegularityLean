module

public import EllipticRegularity.Parabolic.Nash.CauchyUniquenessProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Uniqueness for the Cauchy problem (a standard fact used in Section 5.3): two energy solutions with the same `L²` datum agree at every time
(as `L²_loc` classes) and have a.e. equal gradients. -/
theorem cauchyUniqueness (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u v : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hv : IsCauchySolution a s T f v) :
    (∀ t ∈ Icc s T, ∀ᵐ x : Vec d, u.toFun (x, t) = v.toFun (x, t)) ∧
      ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)), u.grad z = v.grad z := by exact PDE.Ch5NashCauchyUniquenessProof.result d lam Lam a s T hsT ha f hf u v hu hv

end PDE
