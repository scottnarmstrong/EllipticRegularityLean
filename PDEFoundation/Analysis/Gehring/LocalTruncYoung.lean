module

public import PDEFoundation.Analysis.Gehring.LocalTruncated

/-!
# Hölder and Young steps for the localized truncated estimate

`I_L(B_ρ) ≤ T^ε ∫ g + (1/4) I_L(B_R) + 8^ε (2 B N_σ)^{1+ε} ∫ h^{1+ε}`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- Young's inequality in the form `X a^{ε/(1+ε)} ≤ a/8 + 8^ε X^{1+ε}`. -/
theorem young_real {X a ε : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (hε : 0 < ε) :
    X * a ^ (ε / (1 + ε)) ≤ a / 8 + 8 ^ ε * X ^ (1 + ε) := by
  have hp : 0 < 1 + ε := by linarith
  have hpe : (1 + ε) * (ε / (1 + ε)) = ε := by field_simp
  by_cases h : a ≤ 8 ^ (1 + ε) * X ^ (1 + ε)
  · have h1 : a ^ (ε / (1 + ε)) ≤ (8 ^ (1 + ε) * X ^ (1 + ε)) ^ (ε / (1 + ε)) :=
      Real.rpow_le_rpow ha h (by positivity)
    have h2 : (8 ^ (1 + ε) * X ^ (1 + ε)) ^ (ε / (1 + ε)) = 8 ^ ε * X ^ ε := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul hX, hpe]
    have h3 : X * X ^ ε = X ^ (1 + ε) := by
      rw [Real.rpow_add' hX hp.ne', Real.rpow_one]
    calc X * a ^ (ε / (1 + ε)) ≤ X * (8 ^ ε * X ^ ε) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hX
      _ = 8 ^ ε * (X * X ^ ε) := by ring
      _ = 8 ^ ε * X ^ (1 + ε) := by rw [h3]
      _ ≤ a / 8 + 8 ^ ε * X ^ (1 + ε) := by linarith
  · push Not at h
    have h8 : (0 : ℝ) < 8 ^ (1 + ε) := by positivity
    have h1 : X ^ (1 + ε) ≤ a / 8 ^ (1 + ε) := by
      rw [le_div_iff₀ h8]; linarith
    have h2 : X ≤ a ^ (1 / (1 + ε)) / 8 := by
      have h3 : (X ^ (1 + ε)) ^ (1 / (1 + ε)) ≤ (a / 8 ^ (1 + ε)) ^ (1 / (1 + ε)) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      rw [← Real.rpow_mul hX, mul_one_div_cancel hp.ne', Real.rpow_one,
        Real.div_rpow ha h8.le, ← Real.rpow_mul (by norm_num), mul_one_div_cancel hp.ne',
        Real.rpow_one] at h3
      exact h3
    have h4 : a ^ (1 / (1 + ε)) * a ^ (ε / (1 + ε)) = a := by
      rw [← Real.rpow_add' ha (by positivity), ← add_div, div_self hp.ne', Real.rpow_one]
    have h5 : 0 ≤ a ^ (ε / (1 + ε)) := Real.rpow_nonneg ha _
    calc X * a ^ (ε / (1 + ε)) ≤ (a ^ (1 / (1 + ε)) / 8) * a ^ (ε / (1 + ε)) :=
          mul_le_mul_of_nonneg_right h2 h5
      _ = a / 8 := by rw [div_mul_eq_mul_div, h4]
      _ ≤ a / 8 + 8 ^ ε * X ^ (1 + ε) := by
          have : 0 ≤ 8 ^ ε * X ^ (1 + ε) := by positivity
          linarith

/-- Young's inequality in `ℝ≥0∞` for finite quantities. -/
theorem young_ennreal {X I : ℝ≥0∞} (hX : X ≠ ⊤) (hI : I ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    X * I ^ (ε / (1 + ε)) ≤ ENNReal.ofReal (1 / 8) * I + ENNReal.ofReal (8 ^ ε) * X ^ (1 + ε) := by
  have hp : 0 < 1 + ε := by linarith
  have he : 0 ≤ ε / (1 + ε) := by positivity
  have hx0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  have hy := young_real hx0 ha0 hε
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hI,
    ENNReal.ofReal_rpow_of_nonneg ha0 he, ← ENNReal.ofReal_mul hx0,
    ENNReal.ofReal_rpow_of_nonneg hx0 hp.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc X.toReal * I.toReal ^ (ε / (1 + ε)) ≤ I.toReal / 8 + 8 ^ ε * X.toReal ^ (1 + ε) := hy
    _ = _ := by ring

theorem eLpNorm_rpow_eq_lintegral {h : Vec d → ℝ} (hh0 : ∀ x, 0 ≤ h x)
    (hhm : AEMeasurable h volume) {ε : ℝ} (hε : 0 < ε) :
    (eLpNorm h (ENNReal.ofReal (1 + ε)) volume) ^ (1 + ε) =
      ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) := by
  have hp : 0 < 1 + ε := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top
    hhm.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hh0 x)]

/-- **Localized truncated estimate after Hölder and Young.** -/
theorem local_truncated_young (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g) (hg : Integrable g volume)
    (hc : HasCompactSupport g) {σ A B ρ R m ε L : ℝ}
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume) (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hεA : ε ≤ 1 / (8 * gehringG d * A)) (hL : 0 < L) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) R → g x = 0)
    (hm : 0 < m) (hmg : integralAverage (euclideanBall (0 : Vec d) 1) g ≤ m)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) R →
      GehringRH d σ A B g h z r) :
    ∫⁻ x in euclideanBall (0 : Vec d) ρ,
        ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε ≤
      ENNReal.ofReal (((3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m) ^ ε) *
          (∫⁻ x, ENNReal.ofReal (g x)) +
        ENNReal.ofReal (1 / 4) * truncMoment g L ε +
        ENNReal.ofReal (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)) *
          ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) := by
  have hd0 : 0 < d := by omega
  have hG := gehringG_pos d
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ε) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hhl : LocallyIntegrable h volume := hh.locallyIntegrable hp1
  have hhm : AEMeasurable h volume := hhl.aestronglyMeasurable.aemeasurable
  have hεG : ε ≤ 1 / (8 * gehringG d) :=
    hεA.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  have hbase := local_truncated hd hg0 hh0 hgm hg hc hhl hσ hA hB hε hεA hL hρ hρR hR hsupp hm hmg hrh
  have hho := lintegral_mul_truncV_le hd hg0 hh0 hgm hg hhm hε hεG hL
  have hIfin : truncMoment g L ε < ⊤ := truncMoment_lt_top hg0 hg hε.le
  have hnh : eLpNorm h (ENNReal.ofReal (1 + ε)) volume < ⊤ := hh.eLpNorm_lt_top
  set I := truncMoment g L ε with hI
  set nh := eLpNorm h (ENNReal.ofReal (1 + ε)) volume with hnhdef
  set N := gehringN σ d with hN
  have hNpos : 0 < N := gehringN_pos σ hσ d
  have hXfin : ENNReal.ofReal (2 * B * N) * nh ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnh.ne
  have hy := young_ennreal hXfin hIfin.ne hε
  have hstep : ENNReal.ofReal (B * N) * ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε ≤
      ENNReal.ofReal (1 / 8) * I +
        ENNReal.ofReal (8 ^ ε * (2 * B * N) ^ (1 + ε)) * ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) := by
    calc ENNReal.ofReal (B * N) * ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε
        ≤ ENNReal.ofReal (B * N) * (2 * nh * I ^ (ε / (1 + ε))) := by gcongr
      _ = (ENNReal.ofReal (2 * B * N) * nh) * I ^ (ε / (1 + ε)) := by
          have : ENNReal.ofReal (2 * B * N) = 2 * ENNReal.ofReal (B * N) := by
            rw [show 2 * B * N = 2 * (B * N) by ring, ENNReal.ofReal_mul (by norm_num)]
            simp
          rw [this]; ring
      _ ≤ ENNReal.ofReal (1 / 8) * I + ENNReal.ofReal (8 ^ ε) * (ENNReal.ofReal (2 * B * N) * nh) ^ (1 + ε) := hy
      _ = _ := by
          have hnp : nh ^ (1 + ε) = ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) :=
            eLpNorm_rpow_eq_lintegral hh0 hhm hε
          have hB0 : 0 ≤ 2 * B * N := by positivity
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ 1 + ε),
            ENNReal.ofReal_rpow_of_nonneg hB0 (by linarith : (0 : ℝ) ≤ 1 + ε),
            hnp, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  calc _ ≤ _ := hbase
    _ ≤ ENNReal.ofReal (((3 * Real.sqrt d / (R - ρ)) ^ (d + 1) * m) ^ ε) *
          (∫⁻ x, ENNReal.ofReal (g x)) + ENNReal.ofReal (1 / 8) * I +
        (ENNReal.ofReal (1 / 8) * I +
          ENNReal.ofReal (8 ^ ε * (2 * B * N) ^ (1 + ε)) * ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε)) := by
        gcongr
    _ = _ := by
        rw [add_assoc, ← add_assoc (ENNReal.ofReal (1 / 8) * I), ← add_mul,
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
        rw [add_assoc]

end PDE.Gehring
