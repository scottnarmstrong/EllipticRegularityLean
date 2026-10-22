module

public import PDEFoundation.Analysis.Inequalities.Trudinger.Pointwise
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Choice of the splitting radius (Trudinger, Step 4)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

/-- The Lebesgue measure of the unit Euclidean ball, as a real number. -/
noncomputable def unitVol (d : ℕ) : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal

/-- The constant in the pointwise logarithmic Riesz bound. -/
noncomputable def C2 (d : ℕ) : ℝ :=
  2 ^ d * unitVol d + (8 * 2 ^ d * unitVol d) ^ (((d : ℝ) - 1) / d)

theorem unitVol_pos (d : ℕ) : 0 < unitVol d :=
  volume_euclideanBall_toReal_pos (0 : Vec d) one_pos

theorem ofReal_unitVol (d : ℕ) :
    ENNReal.ofReal (unitVol d) = volume (euclideanBall (0 : Vec d) 1) :=
  ENNReal.ofReal_toReal (volume_euclideanBall_ne_top _ zero_le_one)

/-- The pointwise logarithmic bound for the Riesz potential (Trudinger, Steps 2-4). -/
theorem lintegral_riesz_le_log (hd : 2 ≤ d) (x : Vec d) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hLd : ∫⁻ y, f y ^ (d : ℝ) ≤ 1)
    (hsupp : ∀ y, f y ≠ 0 → vecEuclideanNorm (x - y) < 2)
    {m : ℝ} (hm : 0 < m)
    (havg : ∀ ρ : ℝ, 0 < ρ →
      ∫⁻ y in euclideanBall x ρ, f y ≤ ENNReal.ofReal m * volume (euclideanBall x ρ)) :
    ∫⁻ y, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y ≤
      ENNReal.ofReal (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hv := unitVol_pos d
  set θ : ℝ := ((d : ℝ) - 1) / d with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
  set L : ℝ := Real.log (2 + m) with hL
  have hℓ := Real.log_two_gt_d9
  have hLℓ : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0 < L := by linarith
  set T : ℝ := L ^ θ with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hL0 _
  have hT1 : 0.69 < T := by
    rcases le_or_gt 1 L with h1 | h1
    · have := Real.one_le_rpow h1 hθ0.le
      linarith
    · have : L ^ (1 : ℝ) ≤ L ^ θ := Real.rpow_le_rpow_of_exponent_ge hL0 h1.le hθ1
      rw [Real.rpow_one] at this
      linarith
  classical
  have hex : ∃ k : ℕ, (1 / 2 : ℝ) ^ k * m ≤ T := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hT0 hm) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hm] at hn
    exact hn.le
  set k := Nat.find hex with hk
  have hk1 : (1 / 2 : ℝ) ^ k * m ≤ T := Nat.find_spec hex
  have hkb : (k : ℝ) + 1 ≤ 8 * L := by
    rcases hkc : Nat.find hex with _ | j
    · have : (0 : ℕ) = k := hkc.symm
      simp only [← this]; push_cast; linarith
    · have hmin := Nat.find_min hex (m := j) (by omega)
      have hj : T < (1 / 2 : ℝ) ^ j * m := not_le.mp hmin
      have h2j : (2 : ℝ) ^ j < 2 * m := by
        have hp : (0 : ℝ) < 2 ^ j := by positivity
        have : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
        rw [this, one_div, inv_mul_eq_div, lt_div_iff₀ hp] at hj
        nlinarith
      have hlogj : (j : ℝ) * Real.log 2 < Real.log 2 + L := by
        have h3 := Real.log_lt_log (by positivity) (h2j.trans (by linarith : 2 * m < 2 * (2 + m)))
        rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h3
        exact h3
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h4 : (j : ℝ) * 0.69 ≤ j * Real.log 2 := by nlinarith
      have hkj : (k : ℝ) = j + 1 := by
        have : k = j + 1 := hkc
        simp [this]
      rw [hkj]
      linarith
  set ε : ℝ := (1 / 2 : ℝ) ^ k with hε
  have hε0 : 0 < ε := by positivity
  set S : Set (Vec d) :=
    {y | ε ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 2} with hS
  set g : Vec d → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y with hg
  have hgm : Measurable g :=
    (ENNReal.measurable_ofReal.comp ((measurable_norm_sub x).pow_const _)).mul hf
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const (measurable_norm_sub x)).inter
      (measurableSet_lt (measurable_norm_sub x) measurable_const)
  have hpt : ∀ y, g y ≤ (euclideanBall x ε).indicator g y + S.indicator g y := by
    intro y
    by_cases hfy : f y = 0
    · simp [hg, hfy]
    · have h2 := hsupp y hfy
      by_cases hy : vecEuclideanNorm (x - y) < ε
      · rw [Set.indicator_of_mem ((mem_euclideanBall_iff_norm_sub_lt x y hε0).2 hy)]
        exact le_self_add
      · rw [Set.indicator_of_mem (show y ∈ S from ⟨not_lt.mp hy, h2⟩)]
        exact le_add_self
  have hnear := lintegral_near_le hd x hε0 hm.le hf havg
  have hfar := lintegral_far_le hd x hf hLd k
  rw [← hθ] at hfar
  calc ∫⁻ y, g y ≤ ∫⁻ y, ((euclideanBall x ε).indicator g y + S.indicator g y) :=
        lintegral_mono hpt
    _ = (∫⁻ y in euclideanBall x ε, g y) + ∫⁻ y in S, g y := by
        rw [lintegral_add_left (hgm.indicator (measurableSet_euclideanBall _ _)),
          lintegral_indicator (measurableSet_euclideanBall _ _), lintegral_indicator hSm]
    _ ≤ ENNReal.ofReal (2 ^ d * T) * ENNReal.ofReal (unitVol d) +
          ENNReal.ofReal ((8 * 2 ^ d * unitVol d) ^ θ * T) := by
        refine add_le_add ?_ ?_
        · rw [ofReal_unitVol]
          refine hnear.trans (mul_le_mul_left ?_ _)
          exact ENNReal.ofReal_le_ofReal (by
            have : 2 ^ d * ε * m = 2 ^ d * (ε * m) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left hk1 (by positivity))
        · refine hfar.trans ?_
          rw [← ofReal_unitVol, ← ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le]
          refine ENNReal.ofReal_le_ofReal ?_
          refine le_of_le_of_eq (Real.rpow_le_rpow (y := 8 * L * 2 ^ d * unitVol d) (by positivity) ?_ hθ0.le) ?_
          · have : ((k : ℝ) + 1) * 2 ^ d * unitVol d ≤ 8 * L * 2 ^ d * unitVol d := by
              have := unitVol_pos d
              gcongr
            exact this
          · rw [show 8 * L * 2 ^ d * unitVol d = (8 * 2 ^ d * unitVol d) * L by ring,
              Real.mul_rpow (by have := unitVol_pos d; positivity) hL0.le]
    _ = ENNReal.ofReal (C2 d * T) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by
          have := unitVol_pos d; positivity) (by positivity)]
        congr 1
        unfold C2
        ring
