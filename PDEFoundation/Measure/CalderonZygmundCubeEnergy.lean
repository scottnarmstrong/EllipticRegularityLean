module

public import PDEFoundation.Geometry.CalderonZygmundCubeCover
public import PDEFoundation.Sobolev.H1.MeanEnergy

/-! # Energy bound on retained Calderón--Zygmund cube balls -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The normalized energy on the doubled circumscribed ball of a retained root
is bounded by the source `N₂` energy with the exact gap scaling. -/
theorem sqrt_integralAverage_retainedCubeBall_le
    {d : ℕ} (hd : 0 < d) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (g : Vec d → Vec d)
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) t) g)
    (k : calderonZygmundRetainedIndices hd hst) :
    Real.sqrt (integralAverage
        (euclideanBall (boxCenter (calderonZygmundGridBox hd hst k.1))
          (2 * (Real.sqrt d * calderonZygmundCubeSide d s t / 2)))
        (fun x => vecNormSq (g x))) ≤
      Real.sqrt ((2 / (t - s)) ^ d) *
        Real.sqrt ((∫ x in euclideanBall (0 : Vec d) t, vecNormSq (g x)) /
          (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
  let r0 := Real.sqrt d * calderonZygmundCubeSide d s t / 2
  let z := boxCenter (calderonZygmundGridBox hd hst k.1)
  let B := euclideanBall z (2 * r0)
  let Bt := euclideanBall (0 : Vec d) t
  let V := (volume (euclideanBall (0 : Vec d) 1)).toReal
  let A := ∫ x in Bt, vecNormSq (g x)
  have hgap : 0 < t - s := sub_pos.mpr hst
  have hr0 : r0 = (t - s) / 4 := by
    exact calderonZygmund_circumscribedRadius_eq hd s t
  have hR : 0 < 2 * r0 := by rw [hr0]; positivity
  have hsub : B ⊆ Bt := by
    exact euclideanBall_two_mul_circumscribedRadius_retained_subset hd hs hst k
  have hraw : (∫ x in B, vecNormSq (g x)) ≤ A := by
    exact setIntegral_vecNormSq_mono_set hsub hg
  have hA : 0 ≤ A := integral_nonneg fun x => vecNormSq_nonneg _
  have hV : 0 < V := volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num)
  have hvol : (volume B).toReal = ((t - s) / 2) ^ d * V := by
    rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos z hR]
    dsimp only [B, V]
    rw [hr0]
    congr 2
    ring
  have hscale : 0 < ((t - s) / 2) ^ d := pow_pos (by positivity) d
  rw [sqrt_integralAverage_vecNormSq_eq]
  calc
    Real.sqrt (∫ x in B, vecNormSq (g x)) / Real.sqrt (volume B).toReal ≤
        Real.sqrt A / Real.sqrt (volume B).toReal :=
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hraw) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((2 / (t - s)) ^ d) * Real.sqrt (A / V) := by
      rw [hvol, Real.sqrt_mul hscale.le, Real.sqrt_div hA]
      have hpow : (2 / (t - s)) ^ d = 1 / (((t - s) / 2) ^ d) := by
        rw [div_pow, div_pow]
        field_simp
      rw [hpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
      field_simp [(Real.sqrt_pos.mpr hscale).ne', (Real.sqrt_pos.mpr hV).ne']
    _ = _ := by rfl

end

end PDE
