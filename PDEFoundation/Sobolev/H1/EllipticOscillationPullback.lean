module

public import PDEFoundation.Geometry.EuclideanBall.EllipticImage
public import PDEFoundation.Sobolev.H1.EllipticBallEnergy
public import PDEFoundation.Sobolev.H1.LinearMeanOscillation
public import PDEFoundation.Sobolev.H1.MeanOscillationOperator

/-!
# Mean energy and oscillation under elliptic pullback
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem sqrt_volume_ball_div_ellipticImage_le
    {A : Mat d} {Lam r : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hr : 0 < r) (z : Vec d) :
    Real.sqrt (volume (euclideanBall
        (ellipticNormalizerContinuousLinearEquiv hA z) r)).toReal /
      Real.sqrt (volume (ellipticNormalizerContinuousLinearEquiv hA ''
        euclideanBall z r)).toReal ≤
      Real.sqrt ((Real.sqrt Lam) ^ d) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA
  let X := e '' euclideanBall z r
  let I := euclideanBall (e z) (r / Real.sqrt Lam)
  let Y := euclideanBall (e z) r
  have hL : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hA.Lam_pos
  have hIpos : 0 < (volume I).toReal := by
    dsimp [I]
    exact volume_euclideanBall_toReal_pos _ (div_pos hr hL)
  have hXpos : 0 < (volume X).toReal := by
    exact ENNReal.toReal_pos
      (volume_image_linearEquiv_pos e (volume_euclideanBall_pos z hr)).ne'
      (volume_image_linearEquiv_lt_top e
        (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le))).ne
  have hIX : I ⊆ X := by
    simpa only [I, X, e] using euclideanBall_subset_ellipticNormalizer_image hA hr z
  have hvol : (volume I).toReal ≤ (volume X).toReal :=
    ENNReal.toReal_mono
      (volume_image_linearEquiv_lt_top e
        (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le))).ne
      (measure_mono hIX)
  have hsqrt : Real.sqrt (volume I).toReal ≤ Real.sqrt (volume X).toReal :=
    Real.sqrt_le_sqrt hvol
  calc
    Real.sqrt (volume Y).toReal / Real.sqrt (volume X).toReal ≤
        Real.sqrt (volume Y).toReal / Real.sqrt (volume I).toReal :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
        (Real.sqrt_pos.mpr hIpos) hsqrt
    _ = Real.sqrt ((Real.sqrt Lam) ^ d) := by
      dsimp [Y, I]
      rw [← Real.sqrt_div ENNReal.toReal_nonneg,
        volume_euclideanBall_toReal_div_eq_div_pow (e z) (e z)
          (div_pos hr hL) hr]
      congr 2
      field_simp

/-- Pulling a vector field back by the elliptic normalizer and multiplying by
the normalizer preserves native vector `L²` membership and costs only the
elliptic image volume factor in centered and uncentered normalized energy. -/
theorem ellipticNormalizer_pullback_mean_bounds
    {A : Mat d} {Lam r : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hr : 0 < r) (z : Vec d) {g : Vec d → Vec d}
    (hg : MemVectorL2On
      (euclideanBall (ellipticNormalizerContinuousLinearEquiv hA z) r) g) :
    let e := ellipticNormalizerContinuousLinearEquiv hA
    let T := ellipticNormalizer A
    let f : Vec d → Vec d := fun x => matVecMul T (g (e x))
    MemVectorL2On (euclideanBall z r) f ∧
      centeredVectorMeanL2 (euclideanBall z r) f ≤
        Real.sqrt ((Real.sqrt Lam) ^ d) *
          centeredVectorMeanL2 (euclideanBall (e z) r) g ∧
      Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (f x))) ≤
        Real.sqrt ((Real.sqrt Lam) ^ d) *
          Real.sqrt (integralAverage (euclideanBall (e z) r)
            (fun y => vecNormSq (g y))) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hA
  let T := ellipticNormalizer A
  let B := euclideanBall z r
  let X := e '' B
  let Y := euclideanBall (e z) r
  let h : Vec d → Vec d := fun x => g (e x)
  let f : Vec d → Vec d := fun x => matVecMul T (h x)
  have hBX : X ⊆ Y := by
    simpa only [B, X, Y, e] using ellipticNormalizer_image_euclideanBall_subset hA hr z
  have hgX : MemVectorL2On X g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono hBX le_rfl)
  have hh : MemVectorL2On B h := by
    intro i
    exact memLpOn_comp_linearEquiv e (hgX i)
  have hT : ∀ v : Vec d,
      vecEuclideanNorm (matVecMul T v) ≤ vecEuclideanNorm v := by
    intro v
    dsimp [T]
    apply vecEuclideanNorm_ellipticNormalizer_mulVec_le
    intro xi
    simpa using hA.coercive xi
  have hf : MemVectorL2On B f :=
    memVectorL2On_const_matVecMul T hh (delta := 1) (by norm_num) (by simpa using hT)
  have hBpos : 0 < volume B := by simpa only [B] using volume_euclideanBall_pos z hr
  have hBtop : volume B < ∞ := by
    exact lt_top_iff_ne_top.mpr (by simpa only [B] using volume_euclideanBall_ne_top z hr.le)
  have hXpos : 0 < volume X := volume_image_linearEquiv_pos e hBpos
  have hXtop : volume X < ∞ := volume_image_linearEquiv_lt_top e hBtop
  have hYpos : 0 < volume Y := by simpa only [Y] using volume_euclideanBall_pos (e z) hr
  have hYtop : volume Y < ∞ := by
    exact lt_top_iff_ne_top.mpr (by simpa only [Y] using volume_euclideanBall_ne_top (e z) hr.le)
  have hcenterT := centeredVectorMeanL2_const_matVecMul_le
    T hh hBpos hBtop (delta := 1) (by norm_num) (by simpa using hT)
  have hcenterLinear : centeredVectorMeanL2 B h = centeredVectorMeanL2 X g := by
    have hmean : vectorIntegralAverage B h = vectorIntegralAverage X g := by
      funext i
      simpa only [B, X, h, e, vectorIntegralAverage_apply] using
        integralAverage_comp_linearEquiv e hBpos hBtop (fun y => g y i)
    unfold centeredVectorMeanL2
    rw [hmean]
    congr 1
    simpa only [B, X, h, e] using
      integralAverage_comp_linearEquiv e hBpos hBtop
        (fun y => vecNormSq (g y - vectorIntegralAverage X g))
  have hcenterRestrict := centeredVectorMeanL2_mono_set hBX hg
    hXpos hXtop hYpos hYtop
  rw [Real.sqrt_div ENNReal.toReal_nonneg] at hcenterRestrict
  have hvol := sqrt_volume_ball_div_ellipticImage_le hA hr z
  have hcenterFinal : centeredVectorMeanL2 B f ≤
      Real.sqrt ((Real.sqrt Lam) ^ d) * centeredVectorMeanL2 Y g := by
    calc
      centeredVectorMeanL2 B f ≤ centeredVectorMeanL2 B h := by
        simpa only [f, one_mul] using hcenterT
      _ = centeredVectorMeanL2 X g := hcenterLinear
      _ ≤ (Real.sqrt (volume Y).toReal / Real.sqrt (volume X).toReal) *
          centeredVectorMeanL2 Y g := hcenterRestrict
      _ ≤ Real.sqrt ((Real.sqrt Lam) ^ d) * centeredVectorMeanL2 Y g :=
        mul_le_mul_of_nonneg_right (by simpa only [X, Y, e] using hvol)
          (Real.sqrt_nonneg _)
  have henergyT := sqrt_integralAverage_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    hf hh (delta := 1) (by norm_num)
      (Filter.Eventually.of_forall fun x => by simpa using hT (h x))
  have henergyLinear : integralAverage B (fun x => vecNormSq (h x)) =
      integralAverage X (fun y => vecNormSq (g y)) := by
    simpa only [B, X, h, e] using
      integralAverage_comp_linearEquiv e hBpos hBtop (fun y => vecNormSq (g y))
  have henergyRestrict := sqrt_integralAverage_vecNormSq_mono_set hBX
    (ENNReal.toReal_pos hYpos.ne' hYtop.ne) hg
  have henergyFinal : Real.sqrt (integralAverage B (fun x => vecNormSq (f x))) ≤
      Real.sqrt ((Real.sqrt Lam) ^ d) *
        Real.sqrt (integralAverage Y (fun y => vecNormSq (g y))) := by
    calc
      _ ≤ Real.sqrt (integralAverage B (fun x => vecNormSq (h x))) := by
        simpa only [f, one_mul] using henergyT
      _ = Real.sqrt (integralAverage X (fun y => vecNormSq (g y))) := by rw [henergyLinear]
      _ ≤ (Real.sqrt (volume Y).toReal / Real.sqrt (volume X).toReal) *
          Real.sqrt (integralAverage Y (fun y => vecNormSq (g y))) := henergyRestrict
      _ ≤ Real.sqrt ((Real.sqrt Lam) ^ d) *
          Real.sqrt (integralAverage Y (fun y => vecNormSq (g y))) :=
        mul_le_mul_of_nonneg_right (by simpa only [X, Y, e] using hvol)
          (Real.sqrt_nonneg _)
  exact ⟨by simpa only [B, f, h, T, e] using hf,
    by simpa only [B, Y, f, h, T, e] using hcenterFinal,
    by simpa only [B, Y, f, h, T, e] using henergyFinal⟩

end

end PDE
