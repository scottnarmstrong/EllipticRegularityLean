module

public import PDEFoundation.Analysis.Gehring.LocalItRadii

/-!
# The localization iteration for a fixed truncation level

`I_L(B_{1/2}) ≤ 4 ω m^{1+ε} + (4/3) 8^ε (2 B N_σ)^{1+ε} ∫ h^{1+ε}`, where `ω = |B_1|`,
`m = ⨍_{B_1} g`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem lintegral_rpow_lt_top_of_memLp {h : Vec d → ℝ} (hh0 : ∀ x, 0 ≤ h x) {ε : ℝ} (hε : 0 < ε)
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume) :
    ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) < ⊤ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ε) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hhm : AEMeasurable h volume :=
    (hh.locallyIntegrable hp1).aestronglyMeasurable.aemeasurable
  rw [← eLpNorm_rpow_eq_lintegral hh0 hhm hε]
  exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hh.eLpNorm_lt_top.ne

/-- `∫ g = ω m` for `g` supported in `B_1`, in `ℝ≥0∞`. -/
theorem lintegral_eq_ofReal_mul_average {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : Integrable g volume)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) 1 → g x = 0) :
    ∫⁻ x, ENNReal.ofReal (g x) = ENNReal.ofReal ((volume (euclideanBall (0 : Vec d) 1)).toReal *
      integralAverage (euclideanBall (0 : Vec d) 1) g) := by
  have hω := volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  have e1 : ∫ x in euclideanBall (0 : Vec d) 1, g x = ∫ x, g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; exact hsupp x hx
  unfold integralAverage
  rw [← mul_assoc, mul_inv_cancel₀ hω.ne', one_mul, e1,
    ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0)]

/-- The iteration at a fixed truncation level `L`. -/
theorem local_iteration_L (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g) (hg : Integrable g volume)
    (hc : HasCompactSupport g) {σ A B ε L : ℝ}
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume) (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (hεA : ε ≤ 1 / (8 * gehringG d * A)) (hL : 0 < L)
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) 1 → g x = 0)
    (hm : 0 < integralAverage (euclideanBall (0 : Vec d) 1) g)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) 1 →
      GehringRH d σ A B g h z r) :
    truncMomentOn g L ε (euclideanBall (0 : Vec d) (1 / 2)) ≤
      ENNReal.ofReal (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal *
          integralAverage (euclideanBall (0 : Vec d) 1) g ^ (1 + ε) +
        4 / 3 * ((8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)) *
          (∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε)).toReal)) := by
  have hd0 : 0 < d := by omega
  set m := integralAverage (euclideanBall (0 : Vec d) 1) g with hmdef
  set ω := (volume (euclideanBall (0 : Vec d) 1)).toReal with hωdef
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  set κ : ℝ := 8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε) with hκ
  have hN := gehringN_pos σ hσ d
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  set Hraw := ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) with hHraw
  have hHfin : Hraw < ⊤ := lintegral_rpow_lt_top_of_memLp hh0 hε hh
  set Hr := Hraw.toReal with hHr
  set M := ∫⁻ x, ENNReal.ofReal (g x) with hMdef
  have hMeq : M = ENNReal.ofReal (ω * m) := lintegral_eq_ofReal_mul_average hg0 hg hsupp
  have hIfin : truncMoment g L ε < ⊤ := truncMoment_lt_top hg0 hg hε.le
  have hafin : ∀ j : ℕ, truncMomentOn g L ε (euclideanBall (0 : Vec d) (gehringRadius j)) < ⊤ :=
    fun j => lt_of_le_of_lt (truncMomentOn_le_truncMoment _ _ _ _) hIfin
  set a : ℕ → ℝ := fun j => (truncMomentOn g L ε (euclideanBall (0 : Vec d) (gehringRadius j))).toReal
    with ha
  -- the ENNReal recursion
  have hstep : ∀ j : ℕ,
      truncMomentOn g L ε (euclideanBall (0 : Vec d) (gehringRadius j)) ≤
        ENNReal.ofReal (((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε) *
            ENNReal.ofReal (ω * m) +
          ENNReal.ofReal (1 / 4) *
            truncMomentOn g L ε (euclideanBall (0 : Vec d) (gehringRadius (j + 1))) +
          ENNReal.ofReal κ * Hraw := by
    intro j
    have := local_step hd hg0 hh0 hgm hg hc hh hσ hA hB hε hεA hL
      (ρ := gehringRadius j) (R := gehringRadius (j + 1)) (m := m)
      (by linarith [half_le_gehringRadius j]) (gehringRadius_lt j)
      (by linarith [gehringRadius_le (j + 1)]) hm le_rfl hrh
    rw [gehringRadius_threshold, show (∫⁻ x, ENNReal.ofReal (g x)) = ENNReal.ofReal (ω * m) from hMeq] at this
    exact this
  have hrec : ∀ j : ℕ, a j ≤
      ((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε * (ω * m) +
        a (j + 1) / 4 + κ * Hr := by
    intro j
    have h1 := hstep j
    have hfin : ENNReal.ofReal (((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε) *
            ENNReal.ofReal (ω * m) +
          ENNReal.ofReal (1 / 4) *
            truncMomentOn g L ε (euclideanBall (0 : Vec d) (gehringRadius (j + 1))) +
          ENNReal.ofReal κ * Hraw ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hafin (j + 1)).ne⟩, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHfin.ne⟩
    have h2 := ENNReal.toReal_mono hfin h1
    have hnn : 0 ≤ ((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε :=
      Real.rpow_nonneg (by positivity) _
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hafin (j + 1)).ne⟩) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHfin.ne),
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hafin (j + 1)).ne),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hnn, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hκ0] at h2
    calc a j ≤ _ := h2
      _ = _ := by rw [ha]; ring
  have hεd : ((d : ℝ) + 1) * ε ≤ 1 / (32 * 3 ^ d * ((9 : ℝ) / 2) ^ (d + 1)) := by
    have hG := gehringG_pos d
    have hε8 : ε ≤ 1 / (8 * gehringG d) :=
      hεA.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
    have hHpos := gehringH_pos d
    have h3 : (0 : ℝ) < 3 ^ d := by positivity
    have : ((d : ℝ) + 1) * ε ≤ ((d : ℝ) + 1) * (1 / (8 * gehringG d)) :=
      mul_le_mul_of_nonneg_left hε8 (by positivity)
    refine this.trans (le_of_eq ?_)
    unfold gehringG gehringH
    field_simp
    norm_num
  have hK : ∀ j : ℕ, a j ≤ (truncMoment g L ε).toReal := fun j =>
    ENNReal.toReal_mono hIfin.ne (truncMomentOn_le_truncMoment _ _ _ _)
  have hres := iteration_sum_le d hε.le hm.le hω0 (by positivity) hεd hK hrec
  have hres' : a 0 ≤ 4 * ω * m ^ (1 + ε) + 4 / 3 * (κ * Hr) := hres
  have h0 : truncMomentOn g L ε (euclideanBall (0 : Vec d) (1 / 2)) =
      ENNReal.ofReal (a 0) := by
    rw [ha]
    simp only [gehringRadius_zero]
    have h1 := hafin 0
    rw [gehringRadius_zero] at h1
    rw [ENNReal.ofReal_toReal h1.ne]
  rw [h0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc a 0 ≤ 4 * ω * m ^ (1 + ε) + 4 / 3 * (κ * Hr) := hres'
    _ = _ := by rw [hκ]

end PDE.Gehring
