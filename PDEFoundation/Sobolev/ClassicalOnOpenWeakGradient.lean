module

public import PDEFoundation.Analysis.CompactSupportLocalIBP
public import PDEFoundation.Sobolev.ClassicalGradient

@[expose] public section

namespace PDE

/-- A function classically C1 on an open domain has its actual classical
coordinate gradient as weak gradient on that domain. -/
theorem HasWeakGradientOn.of_contDiffOn
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    HasWeakGradientOn U f (classicalGradient f) := by
  intro i
  apply hasWeakPartialDerivOn_iff_forall_testFunction.mpr
  intro φ
  exact integral_mul_weakTestFunction_partialDeriv_eq_neg_integral_fderiv_mul hU hf φ i

end PDE
