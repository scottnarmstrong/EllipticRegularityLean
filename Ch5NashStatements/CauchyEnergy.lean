module

public import EllipticRegularity.Parabolic.Nash.CauchyEnergyProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Global energy identity (a standard fact used in Section 5.3; hence `L²` contraction):
`∫ u(t)² + 2 ∫∫_{(s,t]} ∇u·a∇u = ∫ f²`, both sides finite, in `[0,∞]`-valued form. -/
theorem cauchyEnergyIdentity (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (hu : IsCauchySolution a s T f u)
    (t : ℝ) (ht : t ∈ Icc s T) :
    (∫⁻ x : Vec d, ENNReal.ofReal (u.toFun (x, t) ^ 2)) +
        2 * ∫⁻ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          ENNReal.ofReal (vecDot (u.grad z) (matVecMul (a z) (u.grad z)))
      = ∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2) ∧
    (∫⁻ x : Vec d, ENNReal.ofReal (f x ^ 2)) < ⊤ := by exact PDE.Ch5NashCauchyEnergyProof.result d lam Lam a s T hsT ha f hf u hu t ht

end PDE
