module

public import PDEFoundation.Sobolev.H1.EllipticBallEnergy
public import PDEFoundation.Sobolev.H1.LinearMeanOscillation
public import PDEFoundation.Sobolev.H1.MeanEnergyOperator
public import PDEFoundation.Sobolev.H1.MeanOscillationOperator

/-! # Forcing energy under elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A native vector `L²` forcing field remains locally `L²` after elliptic
normalization. On every ball inside the normalized inner ball, its root mean
square costs only the elliptic image volume factor. -/
theorem ellipticNormalizer_forcing_scale
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hR : 0 < R) (z : Vec d) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F) :
    let e := ellipticNormalizerContinuousLinearEquiv hA
    let T := ellipticNormalizer A
    let rho := R / Real.sqrt Lam
    let F' : Vec d → Vec d := fun y => matVecMul T (F (e.symm y))
    MemVectorL2On (euclideanBall (e z) rho) F' ∧
      ∀ s : ℝ, 0 < s → s ≤ rho →
        Real.sqrt (integralAverage (euclideanBall (e z) s)
          (fun y => vecNormSq (F' y))) ≤
          Real.sqrt ((Real.sqrt Lam) ^ d) *
            Real.sqrt (integralAverage (euclideanBall z (Real.sqrt Lam * s))
              (fun x => vecNormSq (F x))) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hA
  let T := ellipticNormalizer A
  let rho := R / Real.sqrt Lam
  let F' : Vec d → Vec d := fun y => matVecMul T (F (e.symm y))
  have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hA.Lam_pos
  have hrho : 0 < rho := div_pos hR hsqrt
  have hT : ∀ v : Vec d,
      vecEuclideanNorm (matVecMul T v) ≤ vecEuclideanNorm v := by
    intro v
    dsimp [T]
    exact vecEuclideanNorm_ellipticNormalizer_mulVec_le
      (fun xi => by simpa using hA.coercive xi) v
  have hscale : ∀ s : ℝ, 0 < s → s ≤ rho →
      MemVectorL2On (euclideanBall (e z) s) F' ∧
        Real.sqrt (integralAverage (euclideanBall (e z) s)
          (fun y => vecNormSq (F' y))) ≤
          Real.sqrt ((Real.sqrt Lam) ^ d) *
            Real.sqrt (integralAverage (euclideanBall z (Real.sqrt Lam * s))
              (fun x => vecNormSq (F x))) := by
    intro s hs hsrho
    let q := Real.sqrt Lam * s
    let B := euclideanBall z q
    let X := e '' B
    let Y := euclideanBall (e z) s
    let G : Vec d → Vec d := fun y => F (e.symm y)
    have hq : 0 < q := mul_pos hsqrt hs
    have hqR : q ≤ R := by
      have := mul_le_mul_of_nonneg_left hsrho hsqrt.le
      dsimp [rho] at this
      dsimp [q]
      calc
        Real.sqrt Lam * s ≤ Real.sqrt Lam * (R / Real.sqrt Lam) := this
        _ = R := by field_simp [hsqrt.ne']
    have hBR : B ⊆ euclideanBall z R := by
      exact euclideanBall_mono hq.le hqR
    have hFB : MemVectorL2On B F := fun i =>
      (hF i).mono_measure (Measure.restrict_mono hBR le_rfl)
    have hG : MemVectorL2On X G := by
      simpa only [B, X, G, e] using memVectorL2On_comp_symm_linearEquiv e hFB
    have hF'X : MemVectorL2On X F' := by
      apply memVectorL2On_const_matVecMul T hG (delta := 1) (by norm_num)
      simpa only [one_mul] using hT
    have hYX : Y ⊆ X := by
      have hinner := euclideanBall_subset_ellipticNormalizer_image hA hq z
      have heq : q / Real.sqrt Lam = s := by
        dsimp [q]
        field_simp [hsqrt.ne']
      simpa only [Y, X, B, e, heq] using hinner
    have hF'Y : MemVectorL2On Y F' := fun i =>
      (hF'X i).mono_measure (Measure.restrict_mono hYX le_rfl)
    have hXpos : 0 < volume X := by
      exact volume_image_linearEquiv_pos e (volume_euclideanBall_pos z hq)
    have hXtop : volume X < ∞ := by
      exact volume_image_linearEquiv_lt_top e
        (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hq.le))
    have hXreal : 0 < (volume X).toReal :=
      ENNReal.toReal_pos hXpos.ne' hXtop.ne
    have hrestrict := sqrt_integralAverage_vecNormSq_mono_set hYX hXreal hF'X
    have hoperator := sqrt_integralAverage_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
      hF'X hG (delta := 1) (by norm_num)
      (Filter.Eventually.of_forall fun y => by simpa only [F', G, one_mul] using hT (G y))
    have hlinear : integralAverage X (fun y => vecNormSq (G y)) =
        integralAverage B (fun x => vecNormSq (F x)) := by
      symm
      simpa only [B, X, G, e, e.symm_apply_apply] using
        integralAverage_comp_linearEquiv e (volume_euclideanBall_pos z hq)
          (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hq.le))
          (fun y => vecNormSq (F (e.symm y)))
    have hvolume : Real.sqrt (volume X).toReal / Real.sqrt (volume Y).toReal ≤
        Real.sqrt ((Real.sqrt Lam) ^ d) := by
      have hv := sqrt_volume_ellipticImage_div_inner_le hA hq z
      have heq : q / Real.sqrt Lam = s := by
        dsimp [q]
        field_simp [hsqrt.ne']
      simpa only [X, B, Y, e, heq] using hv
    refine ⟨by simpa only [Y] using hF'Y, ?_⟩
    calc
      _ ≤ (Real.sqrt (volume X).toReal / Real.sqrt (volume Y).toReal) *
          Real.sqrt (integralAverage X (fun y => vecNormSq (F' y))) := hrestrict
      _ ≤ Real.sqrt ((Real.sqrt Lam) ^ d) *
          Real.sqrt (integralAverage X (fun y => vecNormSq (F' y))) :=
        mul_le_mul_of_nonneg_right hvolume (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ((Real.sqrt Lam) ^ d) *
          Real.sqrt (integralAverage X (fun y => vecNormSq (G y))) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hoperator)
          (Real.sqrt_nonneg _)
      _ = Real.sqrt ((Real.sqrt Lam) ^ d) *
          Real.sqrt (integralAverage (euclideanBall z (Real.sqrt Lam * s))
            (fun x => vecNormSq (F x))) := by
        rw [hlinear]
  exact ⟨(hscale rho hrho le_rfl).1, fun s hs hsrho => (hscale s hs hsrho).2⟩

end

end PDE
