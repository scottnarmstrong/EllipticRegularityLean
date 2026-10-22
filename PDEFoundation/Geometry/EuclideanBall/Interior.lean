module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Geometry.AxisBox

/-! # Interior balls and enclosing round balls for cubes -/

@[expose] public section

namespace PDE

/-- The triangle inequality keeps a displaced ball inside an outer ball. -/
theorem euclideanBall_subset_of_center_norm_add_le
    {d : ℕ} {c z : Vec d} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hbound : vecEuclideanNorm (z - c) + r ≤ R) :
    euclideanBall z r ⊆ euclideanBall c R := by
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
  have hxz := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hx
  calc
    vecEuclideanNorm (x - c) = vecEuclideanNorm ((x - z) + (z - c)) := by
      congr 1
      abel
    _ ≤ vecEuclideanNorm (x - z) + vecEuclideanNorm (z - c) :=
      vecEuclideanNorm_add_le _ _
    _ < r + vecEuclideanNorm (z - c) := add_lt_add_of_lt_of_le hxz le_rfl
    _ ≤ R := by simpa only [add_comm] using hbound

/-- Every half-unit-ball centre supports an interior ball of radius one half. -/
theorem euclideanBall_half_subset_unit_of_center_mem_half
    {d : ℕ} {z : Vec d} (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) :
    euclideanBall z (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 := by
  apply euclideanBall_subset_of_center_norm_add_le (by norm_num) (by norm_num)
  have hz' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hz
  linarith only [hz']

/-- A centered axis cube fits in a round ball of twice its Euclidean radius
bound. The factor two avoids a boundary convention in the comparison. -/
theorem centeredAxisCube_subset_euclideanBall
    {d : ℕ} (hd : 0 < d) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    centeredAxisCube z r ⊆ euclideanBall z (2 * Real.sqrt d * r) := by
  intro x hx
  rw [centeredAxisCube_eq_metric_ball z hr, Metric.mem_ball, dist_eq_norm] at hx
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mpr
  calc
    vecEuclideanNorm (x - z) ≤ Real.sqrt d * ‖x - z‖ :=
      vecEuclideanNorm_le_sqrt_natCast_mul_norm _
    _ < Real.sqrt d * r := mul_lt_mul_of_pos_left hx hroot
    _ < 2 * Real.sqrt d * r := by nlinarith only [mul_pos hroot hr]

/-- The half-unit ball has supremum-norm diameter at most one. -/
theorem norm_sub_le_one_of_mem_euclideanBall_half
    {d : ℕ} {x y : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hy : y ∈ euclideanBall (0 : Vec d) (1 / 2)) : ‖x - y‖ ≤ 1 := by
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
  simp only [sub_zero] at hx' hy'
  have hxnorm := (norm_le_vecEuclideanNorm x).trans hx'.le
  have hynorm := (norm_le_vecEuclideanNorm y).trans hy'.le
  exact (norm_sub_le x y).trans (by linarith)

end PDE
