module

public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Measure.BallVolume

/-!
# Elementary ball geometry for the logarithmic package
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

theorem vecEuclideanNorm_single_one {d : ℕ} (i0 : Fin d) :
    vecEuclideanNorm (Pi.single i0 (1 : ℝ) : Vec d) = 1 := by
  unfold vecEuclideanNorm
  rw [vecNormSq_eq_sum_sq]
  simp [Pi.single_apply]

/-- Every vector is a nonnegative multiple of a Euclidean unit vector. -/
theorem exists_unit_dir {d : ℕ} (i0 : Fin d) (y : Vec d) :
    ∃ e : Vec d, vecEuclideanNorm e = 1 ∧ y = vecEuclideanNorm y • e := by
  by_cases hy : y = 0
  · refine ⟨Pi.single i0 1, vecEuclideanNorm_single_one i0, ?_⟩
    subst hy
    have : vecEuclideanNorm (0 : Vec d) = 0 := by
      unfold vecEuclideanNorm; simp [vecNormSq, vecDot]
    simp [this]
  · have hpos : 0 < vecEuclideanNorm y := vecEuclideanNorm_pos_iff.mpr hy
    refine ⟨(vecEuclideanNorm y)⁻¹ • y, ?_, ?_⟩
    · rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- If a ball is contained in the ball `B_R(0)` then its center norm plus radius is at most `R`. -/
theorem norm_add_le_of_ball_subset {d : ℕ} (i0 : Fin d) {y : Vec d} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (h : euclideanBall y r ⊆ euclideanBall (0 : Vec d) R) :
    vecEuclideanNorm y + r ≤ R := by
  have hyR : vecEuclideanNorm y < R := by
    have := h (center_mem_euclideanBall y hr)
    simpa using (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp this
  by_contra hcon
  replace hcon := not_le.mp hcon
  obtain ⟨e, he, hye⟩ := exists_unit_dir i0 y
  set t : ℝ := (R - vecEuclideanNorm y + r) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have htr : t < r := by rw [ht]; linarith
  have hz : y + t • e ∈ euclideanBall y r := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
    have : y + t • e - y = t • e := by abel
    rw [this, vecEuclideanNorm_smul, he, abs_of_pos ht0]
    linarith
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp (h hz)
  have hzn : vecEuclideanNorm (y + t • e - 0) = vecEuclideanNorm y + t := by
    have : y + t • e - 0 = (vecEuclideanNorm y + t) • e := by
      rw [sub_zero, add_smul, ← hye]
    rw [this, vecEuclideanNorm_smul, he, abs_of_nonneg (by have := vecEuclideanNorm_nonneg y; linarith)]
    ring
  rw [hzn] at this
  rw [ht] at this
  linarith

end PDE.DGNMLog
