module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Grid

/-!
# Volume of the boundary layers (display (1.36))
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {R : ℝ} {x : Vec d}

/-- The set of points of `B_R(x)` within boundary distance `a R` has volume at most `d a |B_R|`. -/
theorem volume_boundaryLayer_le (hd : 0 < d) (hR : 0 < R) {a : ℝ} (ha : 0 ≤ a) :
    (volume {z ∈ euclideanBall x R | R - vecEuclideanNorm (z - x) ≤ a * R}).toReal ≤
      d * a * (volume (euclideanBall x R)).toReal := by
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have hBpos : 0 < (volume (euclideanBall x R)).toReal :=
    volume_euclideanBall_toReal_pos x hR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases ha1 : 1 ≤ a
  · calc _ ≤ (volume (euclideanBall x R)).toReal :=
          ENNReal.toReal_mono hBtop (measure_mono fun z hz => hz.1)
      _ ≤ d * a * (volume (euclideanBall x R)).toReal :=
          le_mul_of_one_le_left hBpos.le (by nlinarith)
  · push Not at ha1
    set r := R * (1 - a) with hr
    have hrpos : 0 < r := by rw [hr]; exact mul_pos hR (by linarith)
    have hrR : r ≤ R := by rw [hr]; nlinarith
    have hsub : {z ∈ euclideanBall x R | R - vecEuclideanNorm (z - x) ≤ a * R} ⊆
        euclideanBall x R \ euclideanBall x r := by
      rintro z ⟨hz, hza⟩
      refine ⟨hz, fun hz' => ?_⟩
      have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hrpos).mp hz'
      rw [hr] at this; nlinarith
    have hB'sub : euclideanBall x r ⊆ euclideanBall x R := euclideanBall_mono hrpos.le hrR
    have hB'top := volume_euclideanBall_ne_top x hrpos.le
    have hdiff := measure_sdiff hB'sub (measurableSet_euclideanBall x r).nullMeasurableSet hB'top
    have h1 : (volume {z ∈ euclideanBall x R | R - vecEuclideanNorm (z - x) ≤ a * R}).toReal ≤
        (volume (euclideanBall x R \ euclideanBall x r)).toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hBtop (measure_mono sdiff_subset))
        (measure_mono hsub)
    rw [hdiff, ENNReal.toReal_sub_of_le (measure_mono hB'sub) hBtop,
      volume_euclideanBall_toReal_eq_unit_mul_of_pos x hR,
      volume_euclideanBall_toReal_eq_unit_mul_of_pos x hrpos] at h1
    rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos x hR]
    have hω := volume_euclideanBall_toReal_pos (0 : Vec d) (R := 1) one_pos
    have hbern : 1 - d * a ≤ (1 - a) ^ d := by
      have := one_add_mul_le_pow (a := -a) (by linarith) d
      simpa [sub_eq_add_neg] using this
    have hRd : 0 < R ^ d := by positivity
    have : r ^ d = R ^ d * (1 - a) ^ d := by rw [hr, mul_pow]
    rw [this] at h1
    have h2 : R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal -
        R ^ d * (1 - a) ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal ≤
        d * a * (R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
      have := mul_nonneg hRd.le hω.le
      nlinarith [mul_le_mul_of_nonneg_left hbern this]
    exact h1.trans h2

theorem measurableSet_layerUnion (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    MeasurableSet (layerUnion hd hR x k) :=
  MeasurableSet.iUnion fun _ => Box.measurableSet_coe _

/-- Display (1.36): `Σ_{Q ∈ 𝒬_k} |Q| ≤ 2 d 2⁻ᵏ |B|`. -/
theorem volume_layerUnion_le (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    (volume (layerUnion hd hR x k)).toReal ≤
      2 * d / 2 ^ k * (volume (euclideanBall x R)).toReal := by
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have hBpos : 0 < (volume (euclideanBall x R)).toReal :=
    volume_euclideanBall_toReal_pos x hR
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h := volume_boundaryLayer_le (x := x) hd hR (a := 5 / 4 / 2 ^ k) (by positivity)
  rw [show 5 / 4 / (2 : ℝ) ^ k * R = 5 / 4 * (R / 2 ^ k) by ring] at h
  refine (ENNReal.toReal_mono (ne_top_of_le_ne_top hBtop
    (measure_mono fun z (hz : z ∈ {z ∈ euclideanBall x R |
      R - vecEuclideanNorm (z - x) ≤ 5 / 4 * (R / 2 ^ k)}) => hz.1))
    (measure_mono (layerUnion_subset hd hR k))).trans (h.trans ?_)
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply mul_le_mul_of_nonneg_right _ hBpos.le
  rw [show (d : ℝ) * (5 / 4 / 2 ^ k) = (5 / 4 * d) / 2 ^ k by ring]
  rw [div_le_div_iff_of_pos_right hp]; nlinarith

end PDE.JohnNirenbergBall
