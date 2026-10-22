module

public import PDEFoundation.PDE.HolderGradientScale
public import PDEFoundation.PDE.HolderNormalizedEquation
public import PDEFoundation.Regularity.EllipticHolderIdentity

/-! # Gradient scale bounds in canonical elliptic coordinates -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Apply the Hölder gradient iteration on the round ball in canonical
elliptic coordinates. -/
theorem holder_normalized_gradient_scale_bound [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R alpha Ka KF Lam : ℝ}
    (hR : 0 < R) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    {a : CoeffField d} {F : Vec d → Vec d}
    (hell : ∀ x ∈ euclideanBall z R, IsEllipticMatrix 1 Lam (a x))
    (ha : EuclideanMatrixHolderSeminormLE (euclideanBall z R) a alpha Ka)
    (hF : EuclideanFieldHolderSeminormLE (euclideanBall z R) F alpha KF)
    (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (hsmall : (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ alpha * Ka ≤
      alpha * (1 - alpha) /
        (32 * (1 + (2 : ℝ) ^ ((d : ℝ) / 2)))) :
    let hA0 := hell z (center_mem_euclideanBall z hR)
    let e := ellipticNormalizerContinuousLinearEquiv hA0
    let rho := R / Real.sqrt Lam
    let Y := euclideanBall (e z) rho
    let hY : Y ⊆ e '' euclideanBall z R :=
      euclideanBall_subset_ellipticNormalizer_image hA0 hR z
    let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
    ∀ s : ℝ, 0 < s → s ≤ rho →
      Real.sqrt (integralAverage (euclideanBall (e z) s)
          (fun x => vecNormSq (v.grad x))) ≤
        (40 * (2 : ℝ) ^ ((d : ℝ) / 2) *
          (1 + (2 : ℝ) ^ ((d : ℝ) / 2)) / alpha) *
          (2 * Real.sqrt (integralAverage Y (fun x => vecNormSq (v.grad x))) +
            (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ alpha * KF /
              (1 - alpha)) ∧
      (rho / s) ^ alpha * centeredVectorMeanL2
          (euclideanBall (e z) s) v.grad ≤
        16 * (2 : ℝ) ^ ((d : ℝ) / 2) *
          (2 * Real.sqrt (integralAverage Y (fun x => vecNormSq (v.grad x))) +
            (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ alpha * KF /
              (1 - alpha)) := by
  let hA0 := hell z (center_mem_euclideanBall z hR)
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let T := ellipticNormalizer (a z)
  let rho := R / Real.sqrt Lam
  let Y := euclideanBall (e z) rho
  have hY : Y ⊆ e '' euclideanBall z R :=
    euclideanBall_subset_ellipticNormalizer_image hA0 hR z
  let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
  let b : CoeffField d := fun y => T *
    (a (e.symm y) - skewPart (a z)) * matTranspose T
  let F' : Vec d → Vec d := fun y => matVecMul T (F (e.symm y))
  have hrho : 0 < rho := div_pos hR (Real.sqrt_pos.mpr hA0.Lam_pos)
  have hbFull := normalizedCoefficient_holder hA0 halpha0 hKa ha
  have hFFull := normalizedForcing_holder hA0 halpha0 hKF hF
  have hb : EuclideanMatrixHolderSeminormLE Y b alpha
      (Real.sqrt Lam ^ alpha * Ka) := fun x hx y hy =>
    hbFull x (hY hx) y (hY hy)
  have hF' : EuclideanFieldHolderSeminormLE Y F' alpha
      (Real.sqrt Lam ^ alpha * KF) := fun x hx y hy =>
    hFFull x (hY hx) y (hY hy)
  have hb0 : b (e z) = 1 := by
    exact normalizedCoefficient_apply_image_eq_one hA0 rfl
  have hvsol : IsWeakDivergenceFormSolutionOn b Y v 0 F' := by
    exact hsol.ellipticNormalize_innerBall hR hA0
  have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hA0.Lam_pos
  have hcancelKa : rho ^ alpha * (Real.sqrt Lam ^ alpha * Ka) =
      R ^ alpha * Ka := by
    dsimp only [rho]
    rw [Real.div_rpow hR.le hsqrt.le]
    field_simp [(Real.rpow_pos_of_pos hsqrt alpha).ne']
  have hcancelKF : rho ^ alpha * (Real.sqrt Lam ^ alpha * KF) =
      R ^ alpha * KF := by
    dsimp only [rho]
    rw [Real.div_rpow hR.le hsqrt.le]
    field_simp [(Real.rpow_pos_of_pos hsqrt alpha).ne']
  have hiter := holder_gradient_scale_bound hd hrho halpha0 halpha1
    (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg Lam) alpha) hKa)
    (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg Lam) alpha) hKF)
    hb hF' hb0 v hvsol
  have hsmall' :
      (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * rho ^ alpha *
          (Real.sqrt Lam ^ alpha * Ka) ≤
        alpha * (1 - alpha) /
          (32 * (1 + (2 : ℝ) ^ ((d : ℝ) / 2))) := by
    calc
      _ = (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) *
          (rho ^ alpha * (Real.sqrt Lam ^ alpha * Ka)) := by ring
      _ = (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ alpha * Ka := by
        rw [hcancelKa]
        ring
      _ ≤ _ := hsmall
  specialize hiter hsmall'
  have hforce :
      (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * rho ^ alpha *
          (Real.sqrt Lam ^ alpha * KF) /
          (1 - alpha) =
        (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ alpha * KF /
          (1 - alpha) := by
    rw [show (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * rho ^ alpha *
        (Real.sqrt Lam ^ alpha * KF) =
      (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) *
        (rho ^ alpha * (Real.sqrt Lam ^ alpha * KF)) by ring, hcancelKF]
    ring
  simpa only [hA0, e, T, rho, Y, v, hforce] using hiter

end

end PDE
