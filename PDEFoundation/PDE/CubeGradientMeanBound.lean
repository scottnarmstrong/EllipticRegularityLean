module

public import PDEFoundation.Geometry.BoxCircumscribedContainment
public import PDEFoundation.Measure.BoxCircumscribedBallVolume
public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

/-! # Root-cube gradient mean bound -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The gradient mean on an equal-side cube is controlled by the energy on
the doubled circumscribed ball with the exact dimension-only volume factor. -/
theorem vecEuclideanNorm_vectorIntegralAverage_grad_box_le
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (u : H1Function (euclideanBall (boxCenter I)
      (2 * (Real.sqrt d * L / 2)))) :
    vecEuclideanNorm (vectorIntegralAverage (I : Set (Vec d)) u.grad) ≤
      Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
          (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d) *
        Real.sqrt (integralAverage
          (euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)))
          (fun x => vecNormSq (u.grad x))) := by
  let r0 := Real.sqrt d * L / 2
  let Q : Set (Vec d) := (I : Set (Vec d))
  let B1 := euclideanBall (boxCenter I) r0
  let B2 := euclideanBall (boxCenter I) (2 * r0)
  let D := Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
    (Real.sqrt d / 2) ^ d)
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hr0 : 0 < r0 := by
    dsimp only [r0]
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  have hQB2 : Q ⊆ B2 := by
    have hr0' : 0 < Real.sqrt d * L / 2 := by simpa only [r0] using hr0
    dsimp only [Q, B2, r0]
    exact (Box.coe_subset_euclideanClosedBall_boxCenter I L hd hwidth).trans
      (euclideanClosedBall_subset_euclideanBall
        hr0'.le (by linarith))
  have hQpos : 0 < volume Q := by
    dsimp only [Q]
    rw [(Box.coe_ae_eq_Ioo I).measure_eq]
    exact volume_box_Ioo_pos I
  have hQtop : volume Q < ∞ := by
    exact I.measure_coe_lt_top volume
  have hB1pos : 0 < (volume B1).toReal := by
    exact volume_euclideanBall_toReal_pos _ hr0
  have hB2pos : 0 < (volume B2).toReal := by
    exact volume_euclideanBall_toReal_pos _ (by positivity)
  have hgradQ : MemVectorL2On Q u.grad := fun i =>
    memLpOn_mono hQB2 (u.gradMemL2 i)
  have hmean := vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq
    hgradQ hQpos hQtop
  have henergy := sqrt_integralAverage_vecNormSq_mono_set hQB2 hB2pos u.gradMemL2
  have hratio1 : Real.sqrt (volume B1).toReal / Real.sqrt (volume Q).toReal = D := by
    have h := sqrt_volume_euclideanBall_boxCenter_div_box_of_commonWidth
      I L hd hwidth
    rw [Real.sqrt_div ENNReal.toReal_nonneg] at h
    simpa only [B1, Q, r0, D] using h
  have hratio2 : Real.sqrt (volume B2).toReal / Real.sqrt (volume B1).toReal =
      Real.sqrt ((2 : ℝ) ^ d) := by
    have hvol := volume_euclideanBall_toReal_div_eq_div_pow
      (boxCenter I) (boxCenter I) hr0 (by positivity : 0 < 2 * r0)
    have hscale : (2 * r0) / r0 = (2 : ℝ) := by field_simp
    rw [hscale] at hvol
    have h := congrArg Real.sqrt hvol
    rw [Real.sqrt_div ENNReal.toReal_nonneg] at h
    simpa only [B1, B2] using h
  have hratio : Real.sqrt (volume B2).toReal / Real.sqrt (volume Q).toReal =
      D * Real.sqrt ((2 : ℝ) ^ d) := by
    calc
      Real.sqrt (volume B2).toReal / Real.sqrt (volume Q).toReal =
          (Real.sqrt (volume B2).toReal / Real.sqrt (volume B1).toReal) *
            (Real.sqrt (volume B1).toReal / Real.sqrt (volume Q).toReal) := by
        field_simp [(Real.sqrt_pos.mpr hB1pos).ne']
      _ = _ := by rw [hratio1, hratio2, mul_comm]
  exact hmean.trans (by simpa only [hratio, D, B2, r0] using henergy)

end

end PDE
