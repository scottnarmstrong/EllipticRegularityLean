module

public import PDEFoundation.Analysis.Inequalities.Trudinger.RieszLog

/-!
# The distribution function bound (Trudinger, Step 5)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

/-- The Riesz-potential constant `c₁ = 2^d / (d |B₁|)`. -/
noncomputable def rieszConst (d : ℕ) : ℝ := 2 ^ d / (d * unitVol d)

/-- The constant of the Trudinger inequality. -/
noncomputable def trudingerConst (d : ℕ) : ℝ :=
  max (max (2 * 3 ^ d * unitVol d ^ (((d : ℝ) - 1) / d)) (4 * unitVol d))
    ((rieszConst d * C2 d) ^ ((d : ℝ) / ((d : ℝ) - 1)))

theorem trudingerConst_pos (_hd : 2 ≤ d) : 0 < trudingerConst d := by
  have := unitVol_pos d
  exact lt_max_of_lt_left (lt_max_of_lt_right (by positivity))

theorem distribution_le (hd : 2 ≤ d) {G' : Vec d → ℝ} (hG : Measurable G')
    (hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N)
    (hLd : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ^ (d : ℝ) = ENNReal.ofReal N ^ (d : ℝ))
    (hL1 : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ≤
      ENNReal.ofReal N * volume (unitBall d) ^ (((d : ℝ) - 1) / d))
    {w : Vec d → ℝ}
    (hw : ∀ᵐ x ∂volumeOn (unitBall d), w x ≤ rieszConst d *
      ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)
    {t : ℝ} (ht : 0 < t) :
    (volume {z | z ∈ unitBall d ∧ t < w z}).toReal ≤
      trudingerConst d * Real.exp (-(1 / trudingerConst d) *
        (t / N) ^ ((d : ℝ) / ((d : ℝ) - 1))) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hv := unitVol_pos d
  set θ : ℝ := ((d : ℝ) - 1) / d with hθ
  set q : ℝ := (d : ℝ) / ((d : ℝ) - 1) with hq
  have hθ0 : 0 < θ := div_pos hd1 (by linarith)
  have hq0 : 0 < q := div_pos (by linarith) hd1
  have hqθ : q * θ = 1 := by rw [hθ, hq]; field_simp
  set c1 := rieszConst d with hc1
  have hc1pos : 0 < c1 := by rw [hc1, rieszConst]; positivity
  have hC2pos : 0 < C2 d := by unfold C2; positivity
  set C1 : ℝ := c1 * C2 d with hC1
  have hC1pos : 0 < C1 := mul_pos hc1pos hC2pos
  set C := trudingerConst d with hC
  have hCpos : 0 < C := trudingerConst_pos hd
  have hCa : 2 * 3 ^ d * unitVol d ^ θ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCb : 4 * unitVol d ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCc : C1 ^ q ≤ C := le_max_right _ _
  -- the exponent comparison
  set y : ℝ := (t / (N * C1)) ^ q with hy
  have hy0 : 0 ≤ y := by positivity
  have hyle : (1 / C) * (t / N) ^ q ≤ y := by
    have h1 : y = (t / N) ^ q / C1 ^ q := by
      rw [hy, ← Real.div_rpow (by positivity) hC1pos.le]
      congr 1; field_simp
    rw [h1, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hCc
  have hexp : Real.exp (-y) ≤ Real.exp (-(1 / C) * (t / N) ^ q) := by
    apply Real.exp_le_exp.2
    nlinarith
  by_cases hyc : y < Real.log 4
  · -- small `t`
    have hXle : (volume {z | z ∈ unitBall d ∧ t < w z}).toReal ≤ unitVol d := by
      refine ENNReal.toReal_mono (volume_euclideanBall_ne_top _ zero_le_one) ?_
      exact measure_mono fun z hz => hz.1
    have h4 : 1 / 4 ≤ Real.exp (-y) := by
      have : Real.exp (-Real.log 4) ≤ Real.exp (-y) := Real.exp_le_exp.2 (by linarith)
      rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
    calc _ ≤ unitVol d := hXle
      _ ≤ C * Real.exp (-y) := by nlinarith
      _ ≤ _ := by gcongr
  · -- large `t`
    have hyc' : Real.log 4 ≤ y := not_lt.mp hyc
    have hey : 4 ≤ Real.exp y := by
      have := Real.exp_le_exp.2 hyc'
      rwa [Real.exp_log (by norm_num)] at this
    set m : ℝ := Real.exp y - 2 with hm
    have hm0 : 0 < m := by linarith
    have hmhalf : Real.exp y / 2 ≤ m := by linarith
    set f := normalizedMajorant G' N with hf
    set b : Vec d → ℝ := fun y => (f y).toReal with hb
    set M := uncenteredBallMaximal b with hMdef
    have hfm : Measurable f := measurable_normalizedMajorant hG N
    have hL1' := lintegral_normalizedMajorant_le hG hnn hN θ hL1
    have hfin : ∫⁻ y, f y ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0.le
        (volume_euclideanBall_ne_top _ zero_le_one)) hL1'
    have hbint : Integrable b volume :=
      integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hfin
    have hbabs : ∫ x, |b x| ∂volume ≤ unitVol d ^ θ := by
      have : ∫ x, |b x| ∂volume = ∫ x, b x ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => abs_of_nonneg ENNReal.toReal_nonneg)
      rw [this, hb, integral_toReal hfm.aemeasurable (Filter.Eventually.of_forall fun x =>
        lt_top_iff_ne_top.2 (normalizedMajorant_ne_top _ _ _))]
      have := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hθ0.le
        (volume_euclideanBall_ne_top (0 : Vec d) zero_le_one)) hL1'
      rw [← ENNReal.toReal_rpow] at this
      exact this
    have hweak := volume_set_lt_uncenteredBallMaximal_le b m hm0 hbint
    -- the exceptional set
    have hgood : ∀ᵐ x ∂volume, x ∈ unitBall d → w x ≤ c1 *
        ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y :=
      (ae_restrict_iff' (measurableSet_euclideanBall _ _)).1 hw
    have hsub : {z | z ∈ unitBall d ∧ t < w z} ⊆
        {x | ENNReal.ofReal m < M x} ∪ {x | ¬ (x ∈ unitBall d → w x ≤ c1 *
          ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)} := by
      rintro z ⟨hzB, hzt⟩
      by_cases hz : z ∈ unitBall d → w z ≤ c1 *
          ∫ y in unitBall d, vecEuclideanNorm (z - y) ^ ((1 : ℝ) - d) * G' y
      · left
        by_contra hM
        have hM' : M z ≤ ENNReal.ofReal m := not_lt.mp hM
        have hI := integral_riesz_le_log hd hG hnn hN hLd hzB hm0 hM'
        have hlog : Real.log (2 + m) = y := by
          rw [hm, show 2 + (Real.exp y - 2) = Real.exp y by ring, Real.log_exp]
        rw [hlog] at hI
        have hyθ : y ^ θ = t / (N * C1) := by
          rw [hy, ← Real.rpow_mul (by positivity), hqθ, Real.rpow_one]
        rw [hyθ] at hI
        have hwz := hz hzB
        have : w z ≤ t := by
          calc w z ≤ c1 * (N * (C2 d * (t / (N * C1)))) :=
                hwz.trans (mul_le_mul_of_nonneg_left hI hc1pos.le)
            _ = t := by rw [hC1]; field_simp
        linarith
      · right; exact hz
    have hnull : volume {x | ¬ (x ∈ unitBall d → w x ≤ c1 *
          ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)} = 0 :=
      ae_iff.1 hgood
    have hvol : volume {z | z ∈ unitBall d ∧ t < w z} ≤
        ENNReal.ofReal (3 ^ d / m * ∫ x, |b x| ∂volume) := by
      calc _ ≤ volume ({x | ENNReal.ofReal m < M x} ∪ {x | ¬ (x ∈ unitBall d → w x ≤ c1 *
          ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y)}) :=
            measure_mono hsub
        _ ≤ volume {x | ENNReal.ofReal m < M x} + 0 := by
            rw [← hnull]; exact measure_union_le _ _
        _ ≤ _ := by rw [add_zero]; exact hweak
    have hnn' : 0 ≤ 3 ^ d / m * ∫ x, |b x| ∂volume :=
      mul_nonneg (by positivity) (integral_nonneg fun x => abs_nonneg _)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rw [ENNReal.toReal_ofReal hnn'] at hreal
    have hexpy : 0 < Real.exp y := Real.exp_pos y
    calc _ ≤ 3 ^ d / m * ∫ x, |b x| ∂volume := hreal
      _ ≤ 3 ^ d / (Real.exp y / 2) * unitVol d ^ θ := by
          gcongr
      _ = 2 * 3 ^ d * unitVol d ^ θ * Real.exp (-y) := by
          rw [Real.exp_neg]; field_simp
      _ ≤ C * Real.exp (-y) := by gcongr
      _ ≤ _ := by gcongr
