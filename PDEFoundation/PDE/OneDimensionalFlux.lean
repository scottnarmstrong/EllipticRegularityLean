module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.W1p.ZeroGradient

/-! # Constant flux from the one-dimensional weak equation -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- With zero scalar source, the actual one-dimensional weak equation says
that the total flux has zero weak derivative. -/
theorem hasWeakGradientOn_oneDimensional_totalFlux
    {U : Set (Vec 1)} {a : CoeffField 1} {u : H1Function U}
    {F : Vec 1 → Vec 1}
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F) :
    HasWeakGradientOn U
      (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) 0 := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply hasWeakPartialDerivOn_iff_forall_testFunction.mpr
  intro φ
  obtain ⟨htest, heq⟩ := hsol φ
  have hflux : IntegrableOn
      (fun x => (matVecMul (a x) (u.grad x)) 0 * φ.partialDeriv 0 x) U := by
    simpa only [vecDot, Fin.sum_univ_one, WeakTestFunction.grad_apply] using
      htest.flux_integrable
  have hforcing : IntegrableOn (fun x => F x 0 * φ.partialDeriv 0 x) U := by
    simpa only [vecDot, Fin.sum_univ_one, WeakTestFunction.grad_apply] using
      htest.forcing_integrable
  simp only [vecDot, Fin.sum_univ_one, WeakTestFunction.grad_apply,
    Pi.zero_apply, zero_mul, integral_zero, zero_sub] at heq
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]
  simp_rw [add_mul]
  rw [integral_add hflux hforcing, heq]
  exact neg_add_cancel _

/-- An integrable total flux is almost everywhere equal to its domain average
on a positive finite-volume bounded open convex domain. This includes forcing
in `L^p` for `1 < p < 2` whenever the displayed flux is integrable. -/
theorem oneDimensional_totalFlux_ae_eq_integralAverage
    {U : Set (Vec 1)} (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    {a : CoeffField 1} {u : H1Function U} {F : Vec 1 → Vec 1}
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (hflux : IntegrableOn
      (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) U) :
    (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) =ᵐ[volumeOn U]
      fun _ => integralAverage U
        (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) := by
  let q : W1pFunction U 1 :=
    { toFun := fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0
      grad := 0
      memLp := memLp_one_iff_integrable.mpr hflux
      gradMemLp := by
        intro i
        simp
      hasWeakGradient := hasWeakGradientOn_oneDimensional_totalFlux hsol }
  exact W1pFunction.ae_eq_integralAverage_of_grad_ae_eq_zero le_rfl
    (by norm_num) hU hUPos hUTop q (Filter.EventuallyEq.rfl)

end

end PDE
