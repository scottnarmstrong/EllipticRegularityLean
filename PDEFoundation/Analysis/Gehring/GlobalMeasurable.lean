module

public import PDEFoundation.Analysis.Gehring.GlobalReal

/-!
# The global Gehring estimate for measurable `g`
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The explicit constant of the global Gehring estimate: `max (8 G) (3 N_4)`. -/
noncomputable def gehringGlobalC (d : ℕ) : ℝ := max (8 * gehringG d) (3 * gehringN 4 d)

theorem eight_mul_G_le_globalC (d : ℕ) : 8 * gehringG d ≤ gehringGlobalC d := le_max_left _ _

theorem three_mul_N_le_globalC (d : ℕ) : 3 * gehringN 4 d ≤ gehringGlobalC d := le_max_right _ _

theorem one_le_gehringGlobalC (d : ℕ) : 1 ≤ gehringGlobalC d := by
  have := four_mul_succ_le_gehringG d
  have h : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine le_trans ?_ (eight_mul_G_le_globalC d)
  linarith

/-- The global Gehring estimate for measurable `g`, with the explicit constant
`gehringGlobalC d`. -/
theorem global_measurable (hd : 2 ≤ d) {σ A B ε : ℝ} (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (hεA : ε ≤ 1 / (gehringGlobalC d * A))
    {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g)
    (hg : Integrable g volume) (hc : HasCompactSupport g)
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → GehringRH d σ A B g h z r) :
    eLpNorm g (ENNReal.ofReal (1 + ε)) volume ≤
      ENNReal.ofReal (gehringGlobalC d * B) * eLpNorm h (ENNReal.ofReal (1 + ε)) volume := by
  have hd0 : 0 < d := by omega
  have hG := gehringG_pos d
  have hA0 : 0 < A := by linarith
  have hCG := eight_mul_G_le_globalC d
  have hεA' : ε ≤ 1 / (8 * gehringG d * A) :=
    hεA.trans (one_div_le_one_div_of_le (by positivity) (by gcongr))
  have hεG : ε ≤ 1 / (8 * gehringG d) :=
    hεA'.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ε) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hhl : LocallyIntegrable h volume := hh.locallyIntegrable hp1
  have hnh : eLpNorm h (ENNReal.ofReal (1 + ε)) volume < ⊤ := hh.eLpNorm_lt_top
  set nh := eLpNorm h (ENNReal.ofReal (1 + ε)) volume with hnhdef
  set m := nh.toReal with hm
  set N := gehringN σ d with hN
  have hNpos : 0 < N := gehringN_pos σ hσ d
  set e' := ε / (1 + ε) with he'
  have he'0 : 0 ≤ e' := by positivity
  have he'1 : e' < 1 := by rw [he', div_lt_one (by linarith)]; linarith
  set R := 16 / 7 * B * N * m with hR
  have hR0 : 0 ≤ R := by positivity
  -- the uniform bound on the truncated moments
  have hbound : ∀ n : ℕ, truncMoment g ((n : ℝ) + 1) ε ≤ ENNReal.ofReal (R ^ (1 + ε)) := by
    intro n
    have hL : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set I := truncMoment g ((n : ℝ) + 1) ε with hI
    have hIfin : I < ⊤ := truncMoment_lt_top hg0 hg hε.le
    have habs := absorption hd hg0 hh0 hgm hg hc hhl hσ hA hB hε hεA' hL hrh
    have hho := lintegral_mul_truncV_le hd hg0 hh0 hgm hg hhl.aestronglyMeasurable.aemeasurable
      hε hεG hL
    have hchain : I ≤ ENNReal.ofReal (1 / 8) * I +
        ENNReal.ofReal (B * N) * (2 * nh * I ^ e') :=
      habs.trans (add_le_add le_rfl (mul_le_mul_right hho _))
    -- pass to reals
    have hIne : I ≠ ⊤ := hIfin.ne
    have hrhs : ENNReal.ofReal (1 / 8) * I + ENNReal.ofReal (B * N) * (2 * nh * I ^ e') ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by simp) hnh.ne) (ENNReal.rpow_ne_top_of_nonneg he'0 hIne))⟩
    have hreal := ENNReal.toReal_mono hrhs hchain
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by simp) hnh.ne) (ENNReal.rpow_ne_top_of_nonneg he'0 hIne))),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity),
      ← ENNReal.toReal_rpow] at hreal
    simp only [ENNReal.toReal_ofNat] at hreal
    set a := I.toReal with ha
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have h1 : a ≤ a / 8 + (2 * B * N * m) * a ^ e' := by
      calc a ≤ 1 / 8 * a + B * N * (2 * m * a ^ e') := hreal
        _ = _ := by ring
    have h2 := absorb_real ha0 (by positivity) he'1 h1
    have h3 : a ^ (1 - e') = a ^ (1 / (1 + ε)) := by
      congr 1; rw [he']; field_simp; ring
    have h4 : a ≤ R ^ (1 + ε) := by
      have h5 : a ^ (1 / (1 + ε)) ≤ R := by rw [← h3]; linarith
      calc a = (a ^ (1 / (1 + ε))) ^ (1 + ε) := by
            rw [← Real.rpow_mul ha0, one_div_mul_cancel (by linarith), Real.rpow_one]
        _ ≤ R ^ (1 + ε) := Real.rpow_le_rpow (Real.rpow_nonneg ha0 _) h5 (by linarith)
    rw [← ENNReal.ofReal_toReal hIne]
    exact ENNReal.ofReal_le_ofReal h4
  have hint := lintegral_rpow_le_of_truncMoment hgm hε hbound
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top
    hg.aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith)]
  have hnorm : ∫⁻ x, ‖g x‖ₑ ^ (1 + ε) = ∫⁻ x, ENNReal.ofReal (g x) ^ (1 + ε) :=
    lintegral_congr fun x => by rw [Real.enorm_eq_ofReal (hg0 x)]
  rw [hnorm]
  calc (∫⁻ x, ENNReal.ofReal (g x) ^ (1 + ε)) ^ (1 / (1 + ε))
      ≤ (ENNReal.ofReal (R ^ (1 + ε))) ^ (1 / (1 + ε)) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ENNReal.ofReal R := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hR0 _) (by positivity),
          ← Real.rpow_mul hR0, mul_one_div_cancel (by linarith), Real.rpow_one]
    _ ≤ ENNReal.ofReal (gehringGlobalC d * B * m) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 16 / 7 * N ≤ gehringGlobalC d := by
          have := gehringN_le σ hσ d
          have := three_mul_N_le_globalC d
          linarith
        rw [hR]
        have hBm : 0 ≤ B * m := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 hBm]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by have := one_le_gehringGlobalC d; positivity),
          hm, ENNReal.ofReal_toReal hnh.ne]

end PDE.Gehring
