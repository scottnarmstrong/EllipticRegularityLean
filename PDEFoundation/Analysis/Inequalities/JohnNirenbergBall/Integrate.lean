module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.LayerSum

/-!
# Step 4: integrability and the comparison `|(u)_B - (u)_H| ≤ K₁ M`
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {R : ℝ} {x : Vec d} {u : Vec d → ℝ} {M : ℝ}

/-- The scale series `Σ_k (2 ω + K (k + 1)) 2⁻ᵏ` of Step 4. -/
noncomputable def intSeries (d : ℕ) : ℝ :=
  ∑' k : ℕ, (2 * cubeBallRatio d + chainConst d * (k + 1)) * (1 / 2 : ℝ) ^ k

theorem summable_intSeries (d : ℕ) :
    Summable (fun k : ℕ => (2 * cubeBallRatio d + chainConst d * (k + 1)) * (1 / 2 : ℝ) ^ k) := by
  have h0 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have := (h0.mul_left (2 * cubeBallRatio d + chainConst d)).add (h1.mul_left (chainConst d))
  refine this.congr fun k => ?_
  simp only [pow_one]; ring

theorem intSeries_nonneg (hd : 0 < d) : 0 ≤ intSeries d := by
  have := cubeBallRatio_pos hd
  have := chainConst_pos hd
  exact tsum_nonneg fun k => by positivity

section Integrate

variable (hd : 0 < d) (hR : 0 < R) (hloc : LocallyIntegrableOn u (euclideanBall x R) volume)
  (hM : BMOBound (euclideanBall x R) u M) (hMpos : 0 < M)

include hd hR hloc hM hMpos

/-- The integral of `‖u - (u)_H‖ₑ` over `B` is at most `K₁ M |B|`. -/
theorem lintegral_enorm_sub_H_ball_le :
    ∫⁻ z in euclideanBall x R, ‖u z - integralAverage (euclideanBall x (3 * R / 4)) u‖ₑ ≤
      ENNReal.ofReal (2 * d * intSeries d * M) * volume (euclideanBall x R) := by
  set g : Vec d → ℝ≥0∞ := fun z => ‖u z - integralAverage (euclideanBall x (3 * R / 4)) u‖ₑ
  have hω := cubeBallRatio_pos hd
  have hK := chainConst_pos hd
  have hstep : ∀ k : ℕ, ∫⁻ z in layerUnion hd hR x k, g z ≤
      ENNReal.ofReal (2 * d * M * ((2 * cubeBallRatio d + chainConst d * (k + 1)) *
        (1 / 2 : ℝ) ^ k)) * volume (euclideanBall x R) := by
    intro k
    have h1 := lintegral_layerUnion_le hd hR k g
      (ENNReal.ofReal ((2 * cubeBallRatio d + chainConst d * (k + 1)) * M))
      (fun n hn => lintegral_enorm_sub_H_le hd hR hloc hM hMpos hn)
    refine h1.trans ?_
    calc _ ≤ ENNReal.ofReal ((2 * cubeBallRatio d + chainConst d * (k + 1)) * M) *
          (ENNReal.ofReal (2 * d / 2 ^ k) * volume (euclideanBall x R)) := by
          gcongr; exact volume_layerUnion_le_ofReal hd hR k
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [div_eq_mul_inv, ← inv_pow, ← one_div]; ring
  calc ∫⁻ z in euclideanBall x R, g z
      ≤ ∫⁻ z in ⋃ k : ℕ, layerUnion hd hR x k, g z :=
        lintegral_mono_set (ball_subset_iUnion_layerUnion hd hR)
    _ ≤ ∑' k : ℕ, ∫⁻ z in layerUnion hd hR x k, g z := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 * d * M * ((2 * cubeBallRatio d + chainConst d * (k + 1)) *
        (1 / 2 : ℝ) ^ k)) * volume (euclideanBall x R) := ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (2 * d * intSeries d * M) * volume (euclideanBall x R) := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
          (fun k => by positivity) ((summable_intSeries d).mul_left _)]
        congr 2
        rw [tsum_mul_left, intSeries]; ring

/-- Step 4: `u ∈ L¹(B)`. -/
theorem integrableOn_ball : IntegrableOn u (euclideanBall x R) volume := by
  set h := integralAverage (euclideanBall x (3 * R / 4)) u
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have hmeas : AEStronglyMeasurable (fun z => u z - h) (volume.restrict (euclideanBall x R)) :=
    hloc.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hf : IntegrableOn (fun z => u z - h) (euclideanBall x R) volume := by
    refine ⟨hmeas, ?_⟩
    have := lintegral_enorm_sub_H_ball_le hd hR hloc hM hMpos
    exact lt_of_le_of_lt this (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBtop.lt_top)
  have := hf.add (integrableOn_const (μ := volume) (s := euclideanBall x R) (C := h) hBtop)
  exact this.congr_fun (fun z _ => by simp) (measurableSet_euclideanBall x R)

/-- Step 4: `|(u)_B - (u)_H| ≤ K₁ M`. -/
theorem abs_integralAverage_ball_sub_H_le :
    |integralAverage (euclideanBall x R) u - integralAverage (euclideanBall x (3 * R / 4)) u| ≤
      2 * d * intSeries d * M := by
  set h := integralAverage (euclideanBall x (3 * R / 4)) u
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have hBpos := volume_euclideanBall_toReal_pos x hR
  have hint := integrableOn_ball hd hR hloc hM hMpos
  have hf : IntegrableOn (fun z => u z - h) (euclideanBall x R) volume :=
    hint.sub (integrableOn_const hBtop)
  have h1 : ∫ z in euclideanBall x R, ‖u z - h‖ ≤ 2 * d * intSeries d * M *
      (volume (euclideanBall x R)).toReal := by
    rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
    have := lintegral_enorm_sub_H_ball_le hd hR hloc hM hMpos
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop) this
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
      have := intSeries_nonneg hd
      positivity)] at h2
    exact h2
  have h3 : integralAverage (euclideanBall x R) u - h =
      (volume (euclideanBall x R)).toReal⁻¹ * ∫ z in euclideanBall x R, (u z - h) := by
    rw [integral_sub hint (integrableOn_const hBtop), setIntegral_const, smul_eq_mul,
      measureReal_def]
    unfold integralAverage; field_simp
  rw [h3, abs_mul, abs_of_pos (inv_pos.mpr hBpos)]
  calc _ ≤ (volume (euclideanBall x R)).toReal⁻¹ * ∫ z in euclideanBall x R, ‖u z - h‖ := by
        gcongr
        simpa using norm_integral_le_integral_norm (μ := volume.restrict (euclideanBall x R))
          (fun z => u z - h)
    _ ≤ (volume (euclideanBall x R)).toReal⁻¹ *
          (2 * d * intSeries d * M * (volume (euclideanBall x R)).toReal) := by gcongr
    _ = _ := by field_simp

end Integrate

end PDE.JohnNirenbergBall
