module

public import PDEFoundation.Geometry.BoxCenter
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Displacement of centers of dyadic descendant boxes -/

@[expose] public section

namespace PDE

open BoxIntegral Set

/-- The center of a dyadic descendant moves by at most half the difference
between the root and descendant Euclidean diagonal bounds. -/
theorem vecEuclideanNorm_boxCenter_dyadicDescendant_sub_le
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (p : List (Set (Fin d))) :
    vecEuclideanNorm (boxCenter (dyadicDescendant I p) - boxCenter I) ≤
      Real.sqrt d * (L - L / (2 : ℝ) ^ p.length) / 2 := by
  let J := dyadicDescendant I p
  let l := L / (2 : ℝ) ^ p.length
  have hJI : J ≤ I := dyadicDescendant_le I p
  have hb := Box.le_iff_bounds.mp hJI
  have hJwidth (i : Fin d) : J.upper i - J.lower i = l := by
    exact upper_sub_lower_dyadicDescendant_of_commonWidth I L hwidth p i
  have hlL : l ≤ L := by
    let i0 : Fin d := ⟨0, hd⟩
    have := hb.1 i0
    have := hb.2 i0
    linarith [hwidth i0, hJwidth i0]
  have ha : 0 ≤ (L - l) / 2 := by linarith
  have hcoord (i : Fin d) :
      |(boxCenter J - boxCenter I) i| ≤ (L - l) / 2 := by
    rw [abs_le]
    dsimp only [boxCenter, Pi.sub_apply]
    have hlower := hb.1 i
    have hupper := hb.2 i
    constructor <;> linarith [hwidth i, hJwidth i]
  unfold vecEuclideanNorm
  rw [vecNormSq_eq_sum_sq]
  have hsum : ∑ i : Fin d, ((boxCenter J - boxCenter I) i) ^ 2 ≤
      ∑ _i : Fin d, ((L - l) / 2) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _hi
    rw [sq_le_sq]
    simpa only [abs_of_nonneg ha] using hcoord i
  calc
    Real.sqrt (∑ i : Fin d, ((boxCenter J - boxCenter I) i) ^ 2) ≤
        Real.sqrt (∑ _i : Fin d, ((L - l) / 2) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * (L - l) / 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hdR : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      have heq : (d : ℝ) * ((L - l) / 2) ^ 2 =
          (Real.sqrt d * ((L - l) / 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hdR]
      rw [heq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) ha)]
      ring

/-- A ball of the root circumscribed radius around any dyadic descendant
center lies in the ball of twice that radius around the root center. -/
theorem euclideanBall_boxCenter_dyadicDescendant_subset_two_mul
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (p : List (Set (Fin d))) :
    euclideanBall (boxCenter (dyadicDescendant I p)) (Real.sqrt d * L / 2) ⊆
      euclideanBall (boxCenter I) (2 * (Real.sqrt d * L / 2)) := by
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hr : 0 < Real.sqrt d * L / 2 := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  apply euclideanBall_subset_of_center_norm_add_le hr (by positivity)
  have hmove := vecEuclideanNorm_boxCenter_dyadicDescendant_sub_le
    I L hd hwidth p
  have hscale : 0 ≤ L / (2 : ℝ) ^ p.length := by positivity
  calc
    vecEuclideanNorm (boxCenter (dyadicDescendant I p) - boxCenter I) +
        Real.sqrt d * L / 2 ≤
      Real.sqrt d * (L - L / (2 : ℝ) ^ p.length) / 2 +
        Real.sqrt d * L / 2 := by
      simpa only [add_comm] using add_le_add_right hmove (Real.sqrt d * L / 2)
    _ ≤ 2 * (Real.sqrt d * L / 2) := by
      have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      nlinarith

end PDE
