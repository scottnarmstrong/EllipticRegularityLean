module

public import PDEFoundation.Analysis.CompactSupportLocalIBP
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.ClassicalGradient

@[expose] public section

namespace PDE
open MeasureTheory Set

/-- Continuous coefficients times a compactly supported test derivative are
integrable on the test domain. -/
theorem WeakTestFunction.integrableOn_mul_partialDeriv_of_continuousOn
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (φ : WeakTestFunction U) {f : Vec d → ℝ} (hf : ContinuousOn f U)
    (i : Fin d) : IntegrableOn (fun x => f x * φ.partialDeriv i x) U := by
  have hd : Continuous (φ.partialDeriv i) :=
    (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hK : IntegrableOn (fun x => f x * φ.partialDeriv i x) (tsupport φ.toFun) :=
    (hf.mono φ.tsupport_subset |>.mul hd.continuousOn).integrableOn_compact
      φ.hasCompactSupport.isCompact
  apply hK.of_forall_sdiff_eq_zero hU.measurableSet
  intro x hx
  unfold WeakTestFunction.partialDeriv
  rw [fderiv_of_notMem_tsupport ℝ hx.2]
  simp

/-- Local C1 derivatives times the test function are integrable. -/
theorem WeakTestFunction.integrableOn_fderiv_mul_of_contDiffOn
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (φ : WeakTestFunction U) {f : Vec d → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (i : Fin d) :
    IntegrableOn (fun x => (fderiv ℝ f x) (basisVec i) * φ x) U := by
  have hd : ContinuousOn (fun x => (fderiv ℝ f x) (basisVec i)) U := by
    intro x hx
    exact ((hf.contDiffAt (hU.mem_nhds hx)).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const |>.continuousWithinAt
  have hK : IntegrableOn (fun x => (fderiv ℝ f x) (basisVec i) * φ x)
      (tsupport φ.toFun) :=
    ((hd.mono φ.tsupport_subset).mul φ.contDiff.continuous.continuousOn).integrableOn_compact
      φ.hasCompactSupport.isCompact
  apply hK.of_forall_sdiff_eq_zero hU.measurableSet
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport hx.2, mul_zero]

/-- Native coordinate divergence integration by parts for a vector field
classically C1 on the open test domain. -/
theorem integral_vecDot_weakTestFunction_grad_eq_neg_integral_divergence_mul
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (J : Vec d → Vec d) (hJ : ∀ i, ContDiffOn ℝ 1 (fun x => J x i) U)
    (φ : WeakTestFunction U) :
    (∫ x in U, vecDot (J x) (φ.grad x)) =
      -∫ x in U, (∑ i : Fin d, classicalGradient (fun y => J y i) x i) * φ x := by
  change (∫ x in U, ∑ i : Fin d, J x i * φ.partialDeriv i x) = _
  rw [integral_finsetSum Finset.univ
    (fun i _ => φ.integrableOn_mul_partialDeriv_of_continuousOn hU (hJ i).continuousOn i)]
  simp_rw [integral_mul_weakTestFunction_partialDeriv_eq_neg_integral_fderiv_mul hU (hJ _) φ _]
  rw [Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.sum_mul, classicalGradient_apply]
  rw [integral_finsetSum Finset.univ
    (fun i _ => φ.integrableOn_fderiv_mul_of_contDiffOn hU (hJ i) i)]

end PDE
