module

public import PDEFoundation.Analysis.Gehring.TruncNumerics

/-!
# Hölder step: `∫ h V_L^ε ≤ 2 ‖h‖_{1+ε} I_L^{ε/(1+ε)}`
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem measurable_gehringV (g : Vec d → ℝ) : Measurable (gehringV g) := by
  have hlsc : LowerSemicontinuous (cubeMaximal fun y => g y ^ gehringTheta d) :=
    lowerSemicontinuous_iff_isOpen_preimage.2 fun s => isOpen_lt_cubeMaximal _ s
  exact hlsc.measurable.pow_const _

theorem measurable_truncV (g : Vec d → ℝ) (L : ℝ) : Measurable (truncV g L) :=
  (measurable_gehringV g).min measurable_const

/-- **`∫ h V_L^ε ≤ 2 ‖h‖_{L^{1+ε}} I_L^{ε/(1+ε)}`** (Lemma 4.6, second part). -/
theorem lintegral_mul_truncV_le (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g) (hg : Integrable g volume)
    (hhm : AEMeasurable h volume) {ε L : ℝ} (hε : 0 < ε)
    (hεG : ε ≤ 1 / (8 * gehringG d)) (hL : 0 < L) :
    ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε ≤
      2 * eLpNorm h (ENNReal.ofReal (1 + ε)) volume *
        (truncMoment g L ε) ^ (ε / (1 + ε)) := by
  have hd0 : 0 < d := by omega
  have hG := gehringG_pos d
  have hG1 : 1 ≤ gehringG d := by have := four_mul_succ_le_gehringG d; nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have h2 : ε * ((d : ℝ) + 1) ≤ 1 / 32 :=
    (eps_bounds (A := 1) le_rfl hε (by simpa using hεG)).2
  set p : ℝ := 1 + ε with hp
  set q : ℝ := (1 + ε) / ε with hq
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    rw [hp, hq]; field_simp
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    (f := fun x => ENNReal.ofReal (h x)) (g := fun x => (truncV g L x) ^ ε)
    (ENNReal.measurable_ofReal.comp_aemeasurable hhm)
    (((measurable_truncV g L).pow_const ε).aemeasurable)
  have hnorm : (∫⁻ x, ENNReal.ofReal (h x) ^ p) ^ (1 / p) = eLpNorm h (ENNReal.ofReal p) volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top hhm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (by linarith)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (hh0 x)]
  have hq1 : 1 / q = ε / (1 + ε) := by rw [hq]; field_simp
  have hgq : ∫⁻ x, ((truncV g L x) ^ ε) ^ q = ∫⁻ x, (truncV g L x) ^ (1 + ε) := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hq]; field_simp
  have hK := lintegral_truncV_le hd0 hg0 hgm hg hε hL
  have hKG := K_le_G hd hε h2
  have he0 : 0 ≤ ε / (1 + ε) := by positivity
  have he1 : ε / (1 + ε) ≤ 1 / (8 * gehringG d) :=
    (div_le_self hε.le (by linarith)).trans hεG
  calc ∫⁻ x, ENNReal.ofReal (h x) * (truncV g L x) ^ ε
      ≤ (∫⁻ x, ENNReal.ofReal (h x) ^ p) ^ (1 / p) *
          (∫⁻ x, ((truncV g L x) ^ ε) ^ q) ^ (1 / q) := hHold
    _ = eLpNorm h (ENNReal.ofReal p) volume *
          (∫⁻ x, (truncV g L x) ^ (1 + ε)) ^ (ε / (1 + ε)) := by
        rw [hnorm, hgq, hq1]
    _ ≤ eLpNorm h (ENNReal.ofReal p) volume *
          (ENNReal.ofReal (2 * 3 ^ d * (1 + ε) *
            (gehringC d ^ (-(1 - gehringTheta d + ε)) / (1 - gehringTheta d + ε))) *
            truncMoment g L ε) ^ (ε / (1 + ε)) := by
        gcongr
    _ = eLpNorm h (ENNReal.ofReal p) volume *
          ((ENNReal.ofReal (2 * 3 ^ d * (1 + ε) *
            (gehringC d ^ (-(1 - gehringTheta d + ε)) / (1 - gehringTheta d + ε)))) ^ (ε / (1 + ε)) *
            (truncMoment g L ε) ^ (ε / (1 + ε))) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ he0]
    _ ≤ eLpNorm h (ENNReal.ofReal p) volume * (2 * (truncMoment g L ε) ^ (ε / (1 + ε))) := by
        gcongr
        have hpos : 0 ≤ 2 * 3 ^ d * (1 + ε) *
            (gehringC d ^ (-(1 - gehringTheta d + ε)) / (1 - gehringTheta d + ε)) := by
          have := (b_facts hd hε h2).1
          have hb0 : 0 < 1 - gehringTheta d + ε := lt_of_lt_of_le (by positivity) this
          have := gehringC_pos d
          positivity
        rw [ENNReal.ofReal_rpow_of_nonneg hpos he0]
        calc ENNReal.ofReal ((2 * 3 ^ d * (1 + ε) *
            (gehringC d ^ (-(1 - gehringTheta d + ε)) / (1 - gehringTheta d + ε))) ^
              (ε / (1 + ε)))
            ≤ ENNReal.ofReal (2 : ℝ) := by
              refine ENNReal.ofReal_le_ofReal ?_
              calc _ ≤ (gehringG d) ^ (ε / (1 + ε)) :=
                    Real.rpow_le_rpow hpos hKG he0
                _ ≤ 2 := rpow_le_two hG1 he0 he1
          _ = 2 := by simp
    _ = _ := by ring

end PDE.Gehring
