module

public import PDEFoundation.Sobolev.H1.EllipticGradient
public import PDEFoundation.Geometry.EuclideanBall.EllipticImage
public import PDEFoundation.Sobolev.H1.MeanEnergy

/-!
# Energy on the inner ball of an elliptic image

The normalized energy on the inscribed round ball is controlled by the
original ball energy with a constant depending only on dimension and ellipticity.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The square-root volume ratio between an elliptic image and its inscribed
ball costs at most the square root of `(sqrt Lam)^d`. -/
theorem sqrt_volume_ellipticImage_div_inner_le
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hR : 0 < R) (z : Vec d) :
    Real.sqrt (volume (ellipticNormalizerContinuousLinearEquiv hA ''
      euclideanBall z R)).toReal /
      Real.sqrt (volume (euclideanBall
        (ellipticNormalizerContinuousLinearEquiv hA z) (R / Real.sqrt Lam))).toReal ≤
      Real.sqrt ((Real.sqrt Lam) ^ d) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA
  have hL : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hA.Lam_pos
  have hρ : 0 < R / Real.sqrt Lam := div_pos hR hL
  have hv := measure_mono (μ := volume)
    (ellipticNormalizer_image_euclideanBall_subset hA hR z)
  have hvreal : (volume (e '' euclideanBall z R)).toReal ≤
      (volume (euclideanBall (e z) R)).toReal :=
    ENNReal.toReal_mono (volume_euclideanBall_ne_top (e z) hR.le) hv
  calc
    Real.sqrt (volume (e '' euclideanBall z R)).toReal /
        Real.sqrt (volume (euclideanBall (e z) (R / Real.sqrt Lam))).toReal ≤
      Real.sqrt (volume (euclideanBall (e z) R)).toReal /
        Real.sqrt (volume (euclideanBall (e z) (R / Real.sqrt Lam))).toReal :=
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hvreal) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((Real.sqrt Lam) ^ d) := by
      rw [← Real.sqrt_div ENNReal.toReal_nonneg,
        volume_euclideanBall_toReal_div_eq_div_pow (e z) (e z) hρ hR]
      congr 2
      field_simp

/-- Actual transformed gradient energy on the inscribed ball. -/
theorem sqrt_integralAverage_ellipticNormalizer_inner_grad_le
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hR : 0 < R) (z : Vec d) (u : H1Function (euclideanBall z R)) :
    Real.sqrt (integralAverage
      (euclideanBall (ellipticNormalizerContinuousLinearEquiv hA z)
        (R / Real.sqrt Lam))
      (fun y => vecNormSq
        ((u.compLinearEquiv (ellipticNormalizerContinuousLinearEquiv hA)).grad y))) ≤
      (Real.sqrt ((Real.sqrt Lam) ^ d) * Real.sqrt Lam) *
        Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (u.grad x))) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA
  have hpos := volume_euclideanBall_pos z hR
  have htop : volume (euclideanBall z R) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le)
  have hImageReal : 0 < (volume (e '' euclideanBall z R)).toReal :=
    ENNReal.toReal_pos (volume_image_linearEquiv_pos e hpos).ne'
      (volume_image_linearEquiv_lt_top e htop).ne
  have hrestrict := sqrt_integralAverage_vecNormSq_mono_set
    (euclideanBall_subset_ellipticNormalizer_image hA hR z) hImageReal
    (u.compLinearEquiv e).gradMemL2
  have hvolume := sqrt_volume_ellipticImage_div_inner_le hA hR z
  have henergy := u.sqrt_integralAverage_comp_ellipticNormalizer_grad_le hA hpos htop
  calc
    _ ≤ _ := hrestrict
    _ ≤ Real.sqrt ((Real.sqrt Lam) ^ d) *
        Real.sqrt (integralAverage (e '' euclideanBall z R)
          (fun y => vecNormSq ((u.compLinearEquiv e).grad y))) :=
      mul_le_mul_of_nonneg_right hvolume (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((Real.sqrt Lam) ^ d) *
        (Real.sqrt Lam * Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (u.grad x)))) :=
      mul_le_mul_of_nonneg_left henergy (Real.sqrt_nonneg _)
    _ = _ := by ring

end

end PDE
