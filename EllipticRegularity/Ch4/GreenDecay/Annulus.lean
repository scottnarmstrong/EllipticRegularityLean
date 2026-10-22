module

public import EllipticRegularity.Ch4.GreenDecay.Helpers

/-!
# Annuli `A_r = B_r \ B_{r/2}` and the mean-zero source of the decay lemma
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- The annulus `A_r = B_r \ B_{r/2}`. -/
abbrev annulus (d : ℕ) (r : ℝ) : Set (Vec d) := euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)

theorem measurableSet_annulus (r : ℝ) : MeasurableSet (annulus d r) :=
  (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)

theorem annulus_subset (r : ℝ) : annulus d r ⊆ euclideanBall (0 : Vec d) r := Set.sdiff_subset

theorem volume_annulus_ne_top {r : ℝ} (hr : 0 < r) : volume (annulus d r) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_euclideanBall_ne_top 0 hr.le) (measure_mono (annulus_subset r))

/-- The volume of the annulus. -/
theorem volume_annulus_toReal {r : ℝ} (hr : 0 < r) :
    (volume (annulus d r)).toReal =
      (volume (euclideanBall (0 : Vec d) 1)).toReal * (r ^ d - (r / 2) ^ d) := by
  have hr2 : 0 < r / 2 := by positivity
  have hsub : euclideanBall (0 : Vec d) (r / 2) ⊆ euclideanBall (0 : Vec d) r :=
    euclideanBall_mono hr2.le (by linarith)
  have h := measure_sdiff hsub (measurableSet_euclideanBall _ _).nullMeasurableSet
    (volume_euclideanBall_ne_top 0 hr2.le)
  unfold annulus
  rw [h, ENNReal.toReal_sub_of_le (measure_mono hsub) (volume_euclideanBall_ne_top 0 hr.le),
    volume_euclideanBall_toReal_eq_unit_mul_of_pos 0 hr,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos 0 hr2]
  ring

theorem volume_annulus_toReal_pos (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    0 < (volume (annulus d r)).toReal := by
  rw [volume_annulus_toReal hr]
  have hω := volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
  have : (r / 2) ^ d < r ^ d := pow_lt_pow_left₀ (by linarith) (by positivity) hd.ne'
  exact mul_pos hω (by linarith)

theorem volume_annulus_pos (hd : 0 < d) {r : ℝ} (hr : 0 < r) : 0 < volume (annulus d r) := by
  have := volume_annulus_toReal_pos hd hr
  exact (ENNReal.toReal_pos_iff.mp this).1

end

end PDE.Ch4GreenDecay
