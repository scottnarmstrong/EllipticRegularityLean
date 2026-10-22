module

public import PDEFoundation.Analysis.Gehring.LocalItNorm

/-!
# The local Gehring estimate, part (b)

`gehring_local`: the second conjunct of the quantitative Gehring lemma, with the explicit
constant `gehringLocalC d = 2^{d+4} N_4`, for an arbitrary (not necessarily measurable) `g`,
`h`, in the normalized-norm form of the statement `exists_gehring_constant`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- A nonnegative function integrable on `B_1` has a measurable, nonnegative version
vanishing outside `B_1`. -/
theorem exists_measurable_version {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hgI : IntegrableOn g (euclideanBall (0 : Vec d) 1) volume) :
    ∃ g₁ : Vec d → ℝ, Measurable g₁ ∧ (∀ x, 0 ≤ g₁ x) ∧
      (∀ x, x ∉ euclideanBall (0 : Vec d) 1 → g₁ x = 0) ∧
      g =ᵐ[volume.restrict (euclideanBall (0 : Vec d) 1)] g₁ := by
  classical
  set B1 := euclideanBall (0 : Vec d) 1 with hB1
  have hB1m : MeasurableSet B1 := (isOpen_euclideanBall _ _).measurableSet
  set gm := hgI.aemeasurable.mk g with hgm
  have hgmm : Measurable gm := hgI.aemeasurable.measurable_mk
  refine ⟨B1.indicator (fun x => max (gm x) 0), (hgmm.max measurable_const).indicator hB1m,
    fun x => ?_, fun x hx => Set.indicator_of_notMem hx _, ?_⟩
  · by_cases hx : x ∈ B1
    · rw [Set.indicator_of_mem hx]; exact le_max_right _ _
    · rw [Set.indicator_of_notMem hx]
  · filter_upwards [hgI.aemeasurable.ae_eq_mk, ae_restrict_mem hB1m] with x hx hxB
    rw [Set.indicator_of_mem hxB]
    show g x = max (gm x) 0
    have h1 : gm x = g x := hx.symm
    rw [h1, max_eq_left (hg0 x)]

/-- **Quantitative Gehring lemma, part (b)**, with the explicit constant `gehringLocalC d`. -/
theorem gehring_local (hd : 2 ≤ d) {σ : ℝ} (hσ : σ = 2 ∨ σ = 4) {A B ε : ℝ} (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (hεA : ε ≤ 1 / (8 * gehringG d * A))
    {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hgI : IntegrableOn g (euclideanBall (0 : Vec d) 1) volume)
    (hhM : MemLp h (ENNReal.ofReal (1 + ε)) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r →
      centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) 1 → GehringRH d σ A B g h z r) :
    eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal (1 + ε)) g ≤
      ENNReal.ofReal (gehringLocalC d * integralAverage (euclideanBall (0 : Vec d) 1) g) +
        ENNReal.ofReal (gehringLocalC d * B) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal (1 + ε)) h := by
  have hd0 : 0 < d := by omega
  set B1 := euclideanBall (0 : Vec d) 1 with hB1
  set Bh := euclideanBall (0 : Vec d) (1 / 2) with hBh
  have hp : 0 < 1 + ε := by linarith
  have hB1m : MeasurableSet B1 := (isOpen_euclideanBall _ _).measurableSet
  have hB1fin : volume B1 ≠ ⊤ := volume_euclideanBall_ne_top 0 zero_le_one
  have hB1pos : 0 < volume B1 := volume_euclideanBall_pos 0 one_pos
  have hBhfin : volume Bh < ⊤ := (volume_euclideanBall_ne_top 0 (by norm_num)).lt_top
  have hBhsub : Bh ⊆ B1 := Loc.euclideanBall_zero_mono (by norm_num) (by norm_num)
  have hσ1 : 1 ≤ σ := by rcases hσ with h | h <;> rw [h] <;> norm_num
  -- clean versions
  obtain ⟨g₁, hg₁m, hg₁0, hg₁s, hae⟩ := exists_measurable_version hg0 hgI
  have hg₁I : IntegrableOn g₁ B1 volume := hgI.congr_fun_ae hae
  have hg₁i : Integrable g₁ volume :=
    (integrableOn_iff_integrable_of_support_subset (fun x hx => by
      by_contra hxB; exact hx (hg₁s x hxB))).1 hg₁I
  have hg₁c : HasCompactSupport g₁ := by
    refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) zero_le_one)
      fun x hx => hg₁s x fun hxB => hx (euclideanBall_subset_euclideanClosedBall _ _ hxB)
  set h₁ := B1.indicator h with hh₁def
  have hh₁0 : ∀ x, 0 ≤ h₁ x := fun x => Set.indicator_nonneg (fun x _ => hh0 x) x
  have hh₁ : MemLp h₁ (ENNReal.ofReal (1 + ε)) volume :=
    (memLp_indicator_iff_restrict hB1m).2 hhM
  have hrh₁ : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ B1 →
      GehringRH d σ A B g₁ h₁ z r := by
    intro z r hr hsub
    refine GehringRH.congr_eqOn hσ1 hr ?_ ?_ (hrh z r hr hsub)
    · exact ae_restrict_of_ae_restrict_of_subset hsub hae
    · intro x hx
      rw [hh₁def, Set.indicator_of_mem (hsub hx)]
  have hm_eq : integralAverage B1 g₁ = integralAverage B1 g := by
    unfold integralAverage
    congr 1
    exact integral_congr_ae hae.symm
  -- norms as lintegrals
  have hconvL : eLpMeanNormOn Bh (ENNReal.ofReal (1 + ε)) g =
      ((volume Bh)⁻¹ * ∫⁻ x in Bh, ENNReal.ofReal (g₁ x) ^ (1 + ε)) ^ (1 / (1 + ε)) := by
    rw [eLpMeanNormOn_eq_lintegral hBhfin hg0 (hgI.mono_set hBhsub).aestronglyMeasurable hp]
    have : ∫⁻ x in Bh, ENNReal.ofReal (g x) ^ (1 + ε) =
        ∫⁻ x in Bh, ENNReal.ofReal (g₁ x) ^ (1 + ε) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hBhsub hae] with x hx
      rw [hx]
    rw [this]
  have hconvH : eLpMeanNormOn B1 (ENNReal.ofReal (1 + ε)) h =
      ((volume B1)⁻¹ * ∫⁻ x, ENNReal.ofReal (h₁ x) ^ (1 + ε)) ^ (1 / (1 + ε)) := by
    rw [eLpMeanNormOn_eq_lintegral hB1fin.lt_top hh0 hhM.aestronglyMeasurable hp]
    congr 2
    rw [← lintegral_indicator hB1m]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B1
    · simp [hh₁def, hx]
    · simp [hh₁def, hx, ENNReal.zero_rpow_of_pos hp]
  rw [hconvL, hconvH, ← hm_eq]
  set q : ℝ := 1 / (1 + ε) with hq
  have hq0 : 0 < q := by positivity
  have hqp : q * (1 + ε) = 1 := by rw [hq]; field_simp
  set m := integralAverage B1 g₁ with hmdef
  have hm0 : 0 ≤ m := integralAverage_nonneg hB1m fun x _ => hg₁0 x
  set S := ∫⁻ x in Bh, ENNReal.ofReal (g₁ x) ^ (1 + ε) with hSdef
  set Hraw := ∫⁻ x, ENNReal.ofReal (h₁ x) ^ (1 + ε) with hHraw
  rcases hm0.eq_or_lt with hm | hm
  · -- degenerate case: g₁ = 0 a.e.
    have hzero := lintegral_eq_ofReal_mul_average hg₁0 hg₁i hg₁s
    rw [← hmdef, ← hm, mul_zero, ENNReal.ofReal_zero] at hzero
    have hae0 := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hg₁m)).1 hzero
    have hS0 : S = 0 := by
      rw [hSdef]
      have : ∀ᵐ x ∂volume, ENNReal.ofReal (g₁ x) ^ (1 + ε) = 0 := by
        filter_upwards [hae0] with x hx
        simp only [Pi.zero_apply, Function.comp] at hx
        rw [hx, ENNReal.zero_rpow_of_pos hp]
      rw [lintegral_congr_ae (ae_restrict_of_ae this)]
      simp
    rw [hS0, mul_zero, ENNReal.zero_rpow_of_pos hq0]
    exact zero_le
  · have hloc := local_iteration hd hg₁0 hh₁0 hg₁m hg₁i hg₁c hh₁ hσ hA hB hε hεA hg₁s hm hrh₁
    rw [← hmdef, ← hSdef, ← hHraw] at hloc
    set ωE := volume B1 with hωE
    set ω := ωE.toReal with hω
    have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
    have hN := gehringN_pos σ hσ d
    set κ : ℝ := 8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε) with hκ
    have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
    -- the inverse volume of the half ball
    have hvolBh : volume Bh = ENNReal.ofReal ((1 / 2) ^ d) * ωE :=
      volume_euclideanBall_eq_unit_mul_of_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 1 / 2)
    have hVinv : (volume Bh)⁻¹ = ENNReal.ofReal (2 ^ d) * ωE⁻¹ := by
      rw [hvolBh, ENNReal.mul_inv (Or.inr hB1fin) (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 2
      rw [one_div, inv_pow, inv_inv]
    have hfirst : ωE⁻¹ * ENNReal.ofReal (4 * ω * m ^ (1 + ε)) = ENNReal.ofReal (4 * m ^ (1 + ε)) := by
      have : ENNReal.ofReal (4 * ω * m ^ (1 + ε)) = ωE * ENNReal.ofReal (4 * m ^ (1 + ε)) := by
        rw [show 4 * ω * m ^ (1 + ε) = ω * (4 * m ^ (1 + ε)) by ring,
          ENNReal.ofReal_mul hω0, hω, ENNReal.ofReal_toReal hB1fin]
      rw [this, ← mul_assoc, ENNReal.inv_mul_cancel hB1pos.ne' hB1fin, one_mul]
    have hmp : 0 ≤ m ^ (1 + ε) := by positivity
    have halg : (volume Bh)⁻¹ * (ENNReal.ofReal (4 * ω * m ^ (1 + ε)) +
        ENNReal.ofReal (4 / 3 * κ) * Hraw) =
        ENNReal.ofReal (2 ^ (d + 2) * m ^ (1 + ε)) +
          ENNReal.ofReal (2 ^ d * (4 / 3 * κ)) * (ωE⁻¹ * Hraw) := by
      calc (volume Bh)⁻¹ * (ENNReal.ofReal (4 * ω * m ^ (1 + ε)) +
            ENNReal.ofReal (4 / 3 * κ) * Hraw) =
          ENNReal.ofReal (2 ^ d) * (ωE⁻¹ * ENNReal.ofReal (4 * ω * m ^ (1 + ε))) +
            (ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (4 / 3 * κ)) * (ωE⁻¹ * Hraw) := by
            rw [hVinv]; ring
        _ = _ := by
            rw [hfirst, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            rw [show (2 : ℝ) ^ d * (4 * m ^ (1 + ε)) = 2 ^ (d + 2) * m ^ (1 + ε) by
              rw [pow_add]; ring]
    have hq1 : q ≤ 1 := by rw [hq, div_le_one hp]; linarith
    have hεG : ε ≤ 1 / (8 * gehringG d) := by
      have hG := gehringG_pos d
      exact hεA.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
    have hCloc := one_le_gehringN_four d
    have hXle : (2 ^ (d + 2) * m ^ (1 + ε)) ^ q ≤ gehringLocalC d * m := by
      refine (real_X_le hm0 hε).trans ?_
      unfold gehringLocalC
      have h1 : (2 : ℝ) ^ (d + 2) ≤ 2 ^ (d + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ (d + 4) ≤ 2 ^ (d + 4) * gehringN 4 d := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (d+4)]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) hm0
    calc ((volume Bh)⁻¹ * S) ^ q
        ≤ ((volume Bh)⁻¹ * (ENNReal.ofReal (4 * ω * m ^ (1 + ε)) +
            ENNReal.ofReal (4 / 3 * κ) * Hraw)) ^ q := by gcongr
      _ = (ENNReal.ofReal (2 ^ (d + 2) * m ^ (1 + ε)) +
          ENNReal.ofReal (2 ^ d * (4 / 3 * κ)) * (ωE⁻¹ * Hraw)) ^ q := by rw [halg]
      _ ≤ (ENNReal.ofReal (2 ^ (d + 2) * m ^ (1 + ε))) ^ q +
          (ENNReal.ofReal (2 ^ d * (4 / 3 * κ)) * (ωE⁻¹ * Hraw)) ^ q :=
        ENNReal.rpow_add_le_add_rpow _ _ hq0.le hq1
      _ = ENNReal.ofReal ((2 ^ (d + 2) * m ^ (1 + ε)) ^ q) +
          ENNReal.ofReal ((2 ^ d * (4 / 3 * κ)) ^ q) * (ωE⁻¹ * Hraw) ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
      _ ≤ ENNReal.ofReal (gehringLocalC d * m) +
          ENNReal.ofReal (gehringLocalC d * B) * (ωE⁻¹ * Hraw) ^ q := by
        gcongr
        exact real_Y_le hd hσ hB hε hεG

end PDE.Gehring
