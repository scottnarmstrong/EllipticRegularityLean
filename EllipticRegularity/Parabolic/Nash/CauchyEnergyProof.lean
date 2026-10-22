module

public import EllipticRegularity.Parabolic.Cauchy.Energy.GlobalIdentity

/-! # Proof of `PDE.cauchyEnergyIdentity` -/

@[expose] public section

namespace PDE.Ch5NashCauchyEnergyProof

open MeasureTheory Set

theorem result (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    (∫⁻ x : Vec d, ENNReal.ofReal (u.toFun (x, t) ^ 2)) +
        2 * ∫⁻ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          ENNReal.ofReal (vecDot (u.grad z) (matVecMul (a z) (u.grad z)))
      = ∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2) ∧
    (∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2)) < ⊤ :=
  PDE.Parabolic.Cauchy.Energy.cauchyEnergyIdentity d lam Lam a s T hsT ha f hf u hu t ht

end PDE.Ch5NashCauchyEnergyProof
