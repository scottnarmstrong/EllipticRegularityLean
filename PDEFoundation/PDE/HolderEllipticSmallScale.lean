module

public import PDEFoundation.PDE.HolderNormalizedScale
public import PDEFoundation.Sobolev.H1.EllipticBallEnergy
public import PDEFoundation.Sobolev.H1.EllipticGradientPullback

/-! # Small-scale Hölder gradient bounds before elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Pull the normalized Hölder scale estimates back to the original round
ball at radii up to the inscribed normalized radius. -/
theorem holder_elliptic_smallScale_bound [NeZero d]
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
    let rho := R / Real.sqrt Lam
    let L := Real.sqrt ((Real.sqrt Lam) ^ d)
    let D := (2 : ℝ) ^ ((d : ℝ) / 2)
    let H := 1 + 2 * D
    let M0 := Real.sqrt (integralAverage (euclideanBall z R)
      (fun x => vecNormSq (u.grad x)))
    let Q := 2 * L * Real.sqrt Lam * M0 + H * R ^ alpha * KF / (1 - alpha)
    ∀ r : ℝ, 0 < r → r ≤ rho →
      Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x))) ≤
        L * (40 * D * (1 + D) / alpha) * Q ∧
      (R / r) ^ alpha * centeredVectorMeanL2 (euclideanBall z r) u.grad ≤
        L * Real.sqrt Lam ^ alpha * 16 * D * Q := by
  dsimp only
  let hA0 := hell z (center_mem_euclideanBall z hR)
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let rho := R / Real.sqrt Lam
  let L := Real.sqrt ((Real.sqrt Lam) ^ d)
  let D := (2 : ℝ) ^ ((d : ℝ) / 2)
  let H := 1 + 2 * D
  let M0 := Real.sqrt (integralAverage (euclideanBall z R)
    (fun x => vecNormSq (u.grad x)))
  let Y := euclideanBall (e z) rho
  let hY : Y ⊆ e '' euclideanBall z R :=
    euclideanBall_subset_ellipticNormalizer_image hA0 hR z
  let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
  let M0' := Real.sqrt (integralAverage Y (fun x => vecNormSq (v.grad x)))
  let Q' := 2 * M0' + H * R ^ alpha * KF / (1 - alpha)
  let Q := 2 * L * Real.sqrt Lam * M0 + H * R ^ alpha * KF / (1 - alpha)
  have hnorm := holder_normalized_gradient_scale_bound hd hR halpha0 halpha1
    hKa hKF hell ha hF u hsol hsmall
  have hpull := ellipticNormalizer_restrictedGradient_mean_bounds hA0 hR z u
  have hM0' : M0' ≤ L * Real.sqrt Lam * M0 := by
    simpa only [M0', Y, v, L, M0, e, rho] using!
      sqrt_integralAverage_ellipticNormalizer_inner_grad_le hA0 hR z u
  have hgap : 0 < 1 - alpha := sub_pos.mpr halpha1
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hQ' : 0 ≤ Q' := by
    dsimp [Q', M0']
    exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg (mul_nonneg hH (Real.rpow_nonneg hR.le _)) hKF)
        hgap.le)
  have hQ : 0 ≤ Q := by
    dsimp [Q, M0]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL)
        (Real.sqrt_nonneg Lam)) (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg (mul_nonneg hH (Real.rpow_nonneg hR.le _)) hKF)
        hgap.le)
  have hQQ : Q' ≤ Q := by
    dsimp only [Q', Q]
    have hbase : 2 * M0' ≤ 2 * L * Real.sqrt Lam * M0 := by
      calc
      2 * M0' ≤ 2 * (L * Real.sqrt Lam * M0) :=
        mul_le_mul_of_nonneg_left hM0' (by norm_num)
      _ = 2 * L * Real.sqrt Lam * M0 := by ring
    linarith
  intro r hr hrrho
  have hn := hnorm r hr hrrho
  have hp := hpull.2 r hr hrrho
  have hC : 0 ≤ 40 * D * (1 + D) / alpha := by positivity
  have hoscC : 0 ≤ 16 * D := by positivity
  have hscale : (R / r) ^ alpha =
      Real.sqrt Lam ^ alpha * (rho / r) ^ alpha := by
    have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hA0.Lam_pos
    dsimp only [rho]
    rw [show R / r = Real.sqrt Lam * ((R / Real.sqrt Lam) / r) by
      field_simp [hr.ne', hsqrt.ne']]
    exact Real.mul_rpow hsqrt.le (div_nonneg (div_nonneg hR.le hsqrt.le) hr.le)
  constructor
  · calc
      Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x))) ≤
        L * Real.sqrt (integralAverage (euclideanBall (e z) r)
          (fun x => vecNormSq (v.grad x))) := by simpa only [L, e, rho, v] using hp.2
      _ ≤ L * (40 * D * (1 + D) / alpha * Q') :=
        mul_le_mul_of_nonneg_left (by simpa only [D, H, Q', M0', Y] using hn.1) hL
      _ ≤ L * (40 * D * (1 + D) / alpha) * Q := by
        calc
          _ = L * (40 * D * (1 + D) / alpha) * Q' := by ring
          _ ≤ L * (40 * D * (1 + D) / alpha) * Q :=
            mul_le_mul_of_nonneg_left hQQ (mul_nonneg hL hC)
  · rw [hscale]
    calc
      Real.sqrt Lam ^ alpha * (rho / r) ^ alpha *
          centeredVectorMeanL2 (euclideanBall z r) u.grad ≤
        Real.sqrt Lam ^ alpha * (rho / r) ^ alpha *
          (L * centeredVectorMeanL2 (euclideanBall (e z) r) v.grad) :=
        mul_le_mul_of_nonneg_left hp.1
          (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg Lam) alpha)
            (Real.rpow_nonneg (div_nonneg (by positivity) hr.le) alpha))
      _ ≤ Real.sqrt Lam ^ alpha * (L * (16 * D * Q')) := by
        calc
          _ = (Real.sqrt Lam ^ alpha * L) *
              ((rho / r) ^ alpha * centeredVectorMeanL2
                (euclideanBall (e z) r) v.grad) := by ring
          _ ≤ (Real.sqrt Lam ^ alpha * L) * (16 * D * Q') :=
            mul_le_mul_of_nonneg_left
              (by simpa only [D, H, Q', M0', Y] using hn.2)
              (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg Lam) alpha) hL)
          _ = _ := by ring
      _ ≤ L * Real.sqrt Lam ^ alpha * 16 * D * Q := by
        calc
          _ = (L * Real.sqrt Lam ^ alpha * 16 * D) * Q' := by ring
          _ ≤ (L * Real.sqrt Lam ^ alpha * 16 * D) * Q :=
            mul_le_mul_of_nonneg_left hQQ
              (mul_nonneg (mul_nonneg (mul_nonneg hL
                (Real.rpow_nonneg (Real.sqrt_nonneg Lam) alpha)) (by norm_num)) hD)
          _ = _ := by ring

end

end PDE
