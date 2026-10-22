module

public import PDEFoundation.Ambient.MatrixConjugation
public import PDEFoundation.Measure.LinearAverage
public import PDEFoundation.Sobolev.H1.Linear

/-!
# Gradient transport by the elliptic normalizer

This file specializes linear `H¹` transport to the canonical normalizer and
records its exact native gradient formula and normalized energy bound.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private theorem vecDot_nonsingInv_mulVec_basisVec
    (T : Mat d) (hT : matTranspose T = T) (g : Vec d) (i : Fin d) :
    vecDot g (matVecMul T⁻¹ (basisVec i)) = matVecMul T⁻¹ g i := by
  have hInv : matTranspose T⁻¹ = T⁻¹ := by
    calc
      matTranspose T⁻¹ = (matTranspose T)⁻¹ := by
        simpa only [matTranspose] using (Matrix.transpose_nonsing_inv (A := T))
      _ = T⁻¹ := by rw [hT]
  have hb (j : Fin d) : matVecMul T⁻¹ (basisVec i) j = T⁻¹ j i := by
    change T⁻¹.mulVec (Pi.single i 1) j = T⁻¹ j i
    simp [Matrix.mulVec_single, Matrix.col]
  unfold vecDot
  simp_rw [hb]
  calc
    ∑ j, g j * T⁻¹ j i = ∑ j, T⁻¹ j i * g j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = matVecMul T⁻¹ g i := by
      unfold matVecMul
      apply Finset.sum_congr rfl
      intro j _
      have hij := congrArg (fun A : Mat d => A i j) hInv
      simpa only [matTranspose, Matrix.transpose_apply] using congrArg (fun c => c * g j) hij

namespace H1Function

/-- Under the canonical elliptic change of variables, the native weak
gradient is multiplication by the inverse normalizer. -/
theorem comp_ellipticNormalizer_grad
    {A0 : Mat d} {Lam : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    (u : H1Function U) (y : Vec d) :
    (u.compLinearEquiv (ellipticNormalizerContinuousLinearEquiv hA0)).grad y =
      matVecMul (ellipticNormalizer A0)⁻¹
        (u.grad ((ellipticNormalizerContinuousLinearEquiv hA0).symm y)) := by
  funext i
  rw [compLinearEquiv_grad_apply,
    ellipticNormalizerContinuousLinearEquiv_symm_apply]
  exact vecDot_nonsingInv_mulVec_basisVec _
    (ellipticNormalizer_transpose_of_isEllipticMatrix hA0) _ i

/-- Pointwise Euclidean gradient growth under the canonical elliptic change
of variables. -/
theorem vecEuclideanNorm_comp_ellipticNormalizer_grad_le
    {A0 : Mat d} {Lam : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    (u : H1Function U) (y : Vec d) :
    vecEuclideanNorm
        ((u.compLinearEquiv (ellipticNormalizerContinuousLinearEquiv hA0)).grad y) ≤
      Real.sqrt Lam *
        vecEuclideanNorm
          (u.grad ((ellipticNormalizerContinuousLinearEquiv hA0).symm y)) := by
  rw [comp_ellipticNormalizer_grad hA0]
  exact vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le hA0 _

/-- The normalized Euclidean gradient energy grows by at most
`Real.sqrt Lam` under canonical elliptic normalization. -/
theorem sqrt_integralAverage_comp_ellipticNormalizer_grad_le
    {A0 : Mat d} {Lam : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    (u : H1Function U) (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    Real.sqrt (integralAverage
      (ellipticNormalizerContinuousLinearEquiv hA0 '' U)
      (fun y => vecNormSq
        ((u.compLinearEquiv (ellipticNormalizerContinuousLinearEquiv hA0)).grad y))) ≤
      Real.sqrt Lam *
        Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let v := u.compLinearEquiv e
  have hpoint (x : Vec d) :
      vecNormSq (v.grad (e x)) ≤ (Real.sqrt Lam) ^ 2 * vecNormSq (u.grad x) := by
    have hn := vecEuclideanNorm_comp_ellipticNormalizer_grad_le hA0 u (e x)
    simp only [e, ContinuousLinearEquiv.symm_apply_apply] at hn
    rw [← vecEuclideanNorm_sq, ← vecEuclideanNorm_sq]
    have hp := pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) hn 2
    simpa only [e, v, mul_pow] using hp
  have hvcomp : MemVectorL2On U (fun x => v.grad (e x)) := by
    intro i
    exact memLpOn_comp_linearEquiv e (v.gradMemL2 i)
  have hint :
      (∫ x in U, vecNormSq (v.grad (e x))) ≤
        ∫ x in U, (Real.sqrt Lam) ^ 2 * vecNormSq (u.grad x) :=
    integral_mono_ae
      (integrableOn_vecNormSq_of_memVectorL2On hvcomp)
      ((integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2).const_mul _)
      (Filter.Eventually.of_forall hpoint)
  have havg :
      integralAverage U (fun x => vecNormSq (v.grad (e x))) ≤
        (Real.sqrt Lam) ^ 2 * integralAverage U (fun x => vecNormSq (u.grad x)) := by
    unfold integralAverage
    calc
      (volume U).toReal⁻¹ * ∫ x in U, vecNormSq (v.grad (e x)) ≤
          (volume U).toReal⁻¹ *
            ∫ x in U, (Real.sqrt Lam) ^ 2 * vecNormSq (u.grad x) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = (Real.sqrt Lam) ^ 2 *
          ((volume U).toReal⁻¹ * ∫ x in U, vecNormSq (u.grad x)) := by
        rw [integral_const_mul]
        ring
  rw [← integralAverage_comp_linearEquiv e hUpos hUtop
    (fun y => vecNormSq (v.grad y))]
  have hsqrt := Real.sqrt_le_sqrt havg
  calc
    Real.sqrt (integralAverage U (fun x => vecNormSq (v.grad (e x)))) ≤
        Real.sqrt ((Real.sqrt Lam) ^ 2 *
          integralAverage U (fun x => vecNormSq (u.grad x))) := hsqrt
    _ = Real.sqrt Lam *
        Real.sqrt (integralAverage U (fun x => vecNormSq (u.grad x))) := by
      rw [Real.sqrt_mul (sq_nonneg (Real.sqrt Lam)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg Lam)]

end H1Function

end

end PDE
