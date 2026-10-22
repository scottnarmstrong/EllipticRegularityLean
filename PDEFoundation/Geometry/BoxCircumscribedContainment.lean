module

public import PDEFoundation.Geometry.BoxCenter
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Closed circumscribed bounds and retained cube balls -/

@[expose] public section

namespace PDE

open BoxIntegral Set

/-- Every point of a literal half-open equal-side box lies within its closed
Euclidean circumscribed radius from the coordinate midpoint. -/
theorem vecEuclideanNorm_sub_boxCenter_le
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    {x : Vec d} (hx : x ∈ (I : Set (Vec d))) :
    vecEuclideanNorm (x - boxCenter I) ≤ Real.sqrt d * L / 2 := by
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hcoord (i : Fin d) :
      |(x - boxCenter I) i| ≤ L / 2 := by
    rw [abs_le]
    have hxi := hx i
    have hlo := hxi.1
    have hup := hxi.2
    dsimp only [boxCenter, Pi.sub_apply]
    constructor <;> linarith [hwidth i]
  unfold vecEuclideanNorm
  rw [vecNormSq_eq_sum_sq]
  have hsum : ∑ i : Fin d, ((x - boxCenter I) i) ^ 2 ≤
      ∑ _i : Fin d, (L / 2) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _hi
    rw [sq_le_sq]
    simpa only [abs_of_pos (half_pos hL)] using hcoord i
  calc
    Real.sqrt (∑ i : Fin d, ((x - boxCenter I) i) ^ 2) ≤
        Real.sqrt (∑ _i : Fin d, (L / 2) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * L / 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hdR : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      have heq : (d : ℝ) * (L / 2) ^ 2 =
          (Real.sqrt d * (L / 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hdR]
      rw [heq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (half_pos hL).le)]
      ring

/-- The literal half-open box lies in the closed round ball with its exact
Euclidean circumscribed radius. -/
theorem Box.coe_subset_euclideanClosedBall_boxCenter
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    (I : Set (Vec d)) ⊆
      euclideanClosedBall (boxCenter I) (Real.sqrt d * L / 2) := by
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  intro x hx
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mpr
  exact vecEuclideanNorm_sub_boxCenter_le I L hd hwidth hx

/-- If an equal-side box meets `B_s(0)` and three circumscribed radii fit in
the remaining outer radius, its doubled circumscribed ball lies in `B_t(0)`. -/
theorem euclideanBall_two_mul_circumscribedRadius_subset_of_mem
    {d : ℕ} (I : Box (Fin d)) (L s t : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (hs : 0 < s) (y : Vec d) (hyI : y ∈ (I : Set (Vec d)))
    (hys : y ∈ euclideanBall (0 : Vec d) s)
    (hst : s + 3 * (Real.sqrt d * L / 2) ≤ t) :
    euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)) ⊆
      euclideanBall (0 : Vec d) t := by
  let r0 := Real.sqrt d * L / 2
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hr0 : 0 < r0 := by
    dsimp only [r0]
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  have hycenter : vecEuclideanNorm (y - boxCenter I) ≤ r0 := by
    exact vecEuclideanNorm_sub_boxCenter_le I L hd hwidth hyI
  have hy0 : vecEuclideanNorm (y - (0 : Vec d)) < s :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).mp hys
  have hcenter : vecEuclideanNorm (boxCenter I - (0 : Vec d)) < s + r0 := by
    calc
      vecEuclideanNorm (boxCenter I - (0 : Vec d)) =
          vecEuclideanNorm ((boxCenter I - y) + (y - (0 : Vec d))) := by
        congr 1
        module
      _ ≤ vecEuclideanNorm (boxCenter I - y) +
          vecEuclideanNorm (y - (0 : Vec d)) := vecEuclideanNorm_add_le _ _
      _ < r0 + s := add_lt_add_of_le_of_lt
        (by simpa only [vecEuclideanNorm_sub_comm] using hycenter) hy0
      _ = s + r0 := add_comm _ _
  have ht : 0 < t := by
    have : 0 < s + 3 * r0 := by positivity
    exact this.trans_le (by simpa only [r0] using hst)
  apply euclideanBall_subset_of_center_norm_add_le (by positivity) ht
  have hbound : vecEuclideanNorm (boxCenter I - (0 : Vec d)) + 2 * r0 ≤ t := by
    have hlt : vecEuclideanNorm (boxCenter I - (0 : Vec d)) + 2 * r0 <
        s + 3 * r0 := by linarith only [hcenter]
    exact hlt.le.trans (by simpa only [r0] using hst)
  simpa only [r0] using hbound

end PDE
