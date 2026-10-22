/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.EnergyLebesgue

/-! # Pointwise bounds from smooth one-sided averages for `ℝ≥0∞`-valued functions

If `∫ k_h G ≤ R < ∞` for all small one-sided smooth averages, then `G ≤ R` almost everywhere.  The
function `G` need not be locally integrable: we truncate at level `n` and use Lebesgue points of the
truncations.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology PDE.Parabolic.WeakSlice

theorem ae_le_of_ramp_bounds {G : ℝ → ℝ≥0∞} {s t : ℝ} {R : ℝ≥0∞} (hR : R ≠ ⊤)
    (hG : AEMeasurable G (volume.restrict (Ioo s t)))
    (hbound : ∀ t₁ ∈ Ioo s t, ∀ h : ℝ, 0 < h →
      ∫⁻ τ in Ioo s t, ENNReal.ofReal (rampKernel t₁ h τ) * G τ ≤ R) :
    ∀ᵐ τ ∂(volume.restrict (Ioo s t)), G τ ≤ R := by
  let g : ℕ → ℝ → ℝ := fun n =>
    (Ioo s t).indicator (fun τ => (min (G τ) (ENNReal.ofReal n)).toReal)
  have hgm : ∀ n : ℕ, AEStronglyMeasurable (fun τ => (min (G τ) (ENNReal.ofReal n)).toReal)
      (volume.restrict (Ioo s t)) := fun n =>
    (hG.min aemeasurable_const).ennreal_toReal.aestronglyMeasurable
  have hgmeas : ∀ n : ℕ, AEStronglyMeasurable (g n) volume := fun n =>
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).2 (hgm n)
  have hgint : ∀ n : ℕ, Integrable (g n) := by
    intro n
    refine (integrable_indicator_iff measurableSet_Ioo).2 ?_
    refine Integrable.mono' (g := fun _ => (n : ℝ))
      (integrableOn_const (by simp [Real.volume_Ioo])) (hgm n) (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    calc (min (G τ) (ENNReal.ofReal n)).toReal ≤ (ENNReal.ofReal n).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right _ _)
      _ = n := ENNReal.toReal_ofReal n.cast_nonneg
  have hg0 : ∀ (n : ℕ) τ, 0 ≤ g n τ := fun n τ => indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) τ
  have hae : ∀ n : ℕ, ∀ᵐ t₁ : ℝ, t₁ ∈ Ioo s t → g n t₁ ≤ R.toReal := by
    intro n
    filter_upwards [ae_tendsto_rampKernel_integral (hgint n)] with t₁ ht ht1
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (0 : ℝ) < h := hh
    have hf0 : 0 ≤ᵐ[volume] fun τ => rampKernel t₁ h τ * g n τ :=
      Eventually.of_forall fun τ => mul_nonneg (rampKernel_nonneg hh' τ) (hg0 n τ)
    have hfm : AEStronglyMeasurable (fun τ => rampKernel t₁ h τ * g n τ) volume :=
      (rampKernel_continuous t₁ h).aestronglyMeasurable.mul (hgmeas n)
    rw [integral_eq_lintegral_of_nonneg_ae hf0 hfm]
    refine ENNReal.toReal_mono hR ?_
    have hpt : ∀ τ, ENNReal.ofReal (rampKernel t₁ h τ * g n τ) =
        (Ioo s t).indicator (fun τ => ENNReal.ofReal (rampKernel t₁ h τ *
          (min (G τ) (ENNReal.ofReal n)).toReal)) τ := by
      intro τ
      by_cases hτ : τ ∈ Ioo s t
      · simp only [g, indicator_of_mem hτ]
      · simp only [g, indicator_of_notMem hτ, mul_zero, ENNReal.ofReal_zero]
    calc ∫⁻ τ, ENNReal.ofReal (rampKernel t₁ h τ * g n τ)
        = ∫⁻ τ in Ioo s t, ENNReal.ofReal (rampKernel t₁ h τ *
            (min (G τ) (ENNReal.ofReal n)).toReal) := by
          simp_rw [hpt]; exact lintegral_indicator measurableSet_Ioo _
      _ ≤ ∫⁻ τ in Ioo s t, ENNReal.ofReal (rampKernel t₁ h τ) * G τ := by
          refine lintegral_mono fun τ => ?_
          rw [ENNReal.ofReal_mul (rampKernel_nonneg hh' τ), ENNReal.ofReal_toReal
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))]
          exact mul_le_mul' le_rfl (min_le_left _ _)
      _ ≤ R := hbound t₁ ht1 h hh'
  have hall := ae_all_iff.2 hae
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hall] with t₁ h ht1
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨n, hn⟩ := exists_nat_gt R.toReal
  have h1 : (min (G t₁) (ENNReal.ofReal n)).toReal ≤ R.toReal := by
    have := h n ht1
    simpa only [g, indicator_of_mem ht1] using this
  have hRn : R < ENNReal.ofReal n := by
    rw [← ENNReal.ofReal_toReal hR]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a := R)])).2 hn
  have hmin : R < min (G t₁) (ENNReal.ofReal n) := lt_min hlt hRn
  have hfin : min (G t₁) (ENNReal.ofReal n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  have := (ENNReal.toReal_lt_toReal hR hfin).2 hmin
  linarith

end PDE.Parabolic.LocalMax
