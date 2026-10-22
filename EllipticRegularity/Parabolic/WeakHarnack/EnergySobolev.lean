/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyBoundsNeg

/-! # The parabolic Sobolev step for `η v^(r/2)`

From the two energy bounds (the `esssup` bound `S` and the gradient bound) and the slice
Gagliardo-Nirenberg inequality for `η G(u)`, `|G| = v^(r/2)`, we obtain
`∬ η^(2χ) v^(rχ) ≤ C(d) S^(2/d) (r²/2 · Gt + 2X · Pl)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.Chain PDE.Parabolic.LocalMax

variable {d : ℕ}

theorem sobolev_of_energy (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {U : Set (Vec d)}, IsOpen U → volume U ≠ ⊤ →
      ∀ (u : ParH1Function U (Ioc (-1 : ℝ) 0)) {J : Set ℝ}, MeasurableSet J →
      J ⊆ Ioc (-1 : ℝ) 0 →
      (∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z) →
      ∀ {Q : Set (Vec d × ℝ)} {η : Vec d × ℝ → ℝ} {X T : ℝ}, PowCutoff U Q η X T →
      ∀ {r ε : ℝ}, r < 1 → r ≠ 0 → 0 < ε → ∀ S Gt Pl : ℝ≥0∞,
      (∀ᵐ τ ∂(volume.restrict J),
        ∫⁻ x in U, ENNReal.ofReal (η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r) ≤ S) →
      ∫⁻ z in U ×ˢ J,
        ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) ≤ Gt →
      ∫⁻ z in U ×ˢ Ioc (-1 : ℝ) 0,
        ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z) ≤ Pl →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal (η z ^ (2 * ((d : ℝ) + 2) / d) *
          (u.toFun z + ε) ^ (r * (((d : ℝ) + 2) / d))) ≤
        C * S ^ (2 / (d : ℝ)) * (ENNReal.ofReal (r ^ 2 / 2) * Gt + ENNReal.ofReal (2 * X) * Pl) := by
  obtain ⟨C, hC, hGN⟩ := slice_cutoff_comp_gagliardo_nirenberg d hd
  refine ⟨C, hC, ?_⟩
  intro U hU hfin u J hJ hJI hu0 Q η X T hc r ε hr hr0 hε S Gt Pl hS hGt hPl
  obtain ⟨G, hG1, ⟨M, hM0, hM⟩, hGv⟩ := exists_shifted_G hr0 hε hr
  obtain ⟨Kx, hKx, hKxU, hηK⟩ := hc.compact
  have hI0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ J)), 0 ≤ u.toFun z :=
    ae_restrict_of_ae_restrict_of_subset (prod_mono subset_rfl hJI) hu0
  -- slice nonnegativity
  have hslice : ∀ᵐ τ ∂(volume.restrict J), ∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, τ) := by
    have h : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict J)), 0 ≤ u.toFun z := by
      rw [← PDE.Parabolic.Energy.volume_restrict_prod]; exact hI0
    exact PDE.Parabolic.Energy.ae_ae_swap h
  have hS' : ∀ᵐ τ ∂(volume.restrict J),
      ∫⁻ x in U, ENNReal.ofReal ((η (x, τ) * G (u.toFun (x, τ))) ^ 2) ≤ S := by
    filter_upwards [hS, hslice] with τ h1 h2
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr_ae ?_
    filter_upwards [h2] with x hx
    rw [mul_pow, (hGv _ hx).1, mul_comm]
  -- gradient bound
  have hgm : AEMeasurable (fun z => ENNReal.ofReal
      (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z))) (volume.restrict (U ×ˢ J)) := by
    have := integrable_gradTerm u hc.smooth.continuous hc.le_one hc.nonneg hr hε hu0
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (this.aemeasurable.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl)))
  have hD : ∫⁻ z in U ×ˢ J, ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)) ≤
      ENNReal.ofReal (r ^ 2 / 2) * Gt + ENNReal.ofReal (2 * X) * Pl := by
    have hpt : ∀ᵐ z ∂(volume.restrict (U ×ˢ J)),
        ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)) ≤
          ENNReal.ofReal (r ^ 2 / 2) * ENNReal.ofReal
              (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) +
            ENNReal.ofReal (2 * X) * ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z) := by
      filter_upwards [hI0] with z hz
      obtain ⟨hG2, hG'2, -⟩ := hGv _ hz
      have hv : 0 < u.toFun z + ε := by linarith
      have hvr : 0 ≤ (u.toFun z + ε) ^ r := (Real.rpow_pos_of_pos hv r).le
      have hvr2 : 0 ≤ (u.toFun z + ε) ^ (r - 2) := (Real.rpow_pos_of_pos hv (r - 2)).le
      have hN1 := vecNormSq_nonneg (u.grad z)
      have hη2 := sq_nonneg (η z)
      have hX := hc.grad z
      have hbd : vecNormSq (cutoffCompGrad u G η z) ≤
          r ^ 2 / 2 * (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) +
            2 * X * Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
        unfold cutoffCompGrad
        refine (vecNormSq_add_le _ _).trans ?_
        rw [vecNormSq_smul, vecNormSq_smul, mul_pow, hG'2, hG2]
        have hQ : (u.toFun z + ε) ^ r * vecNormSq (parSpaceGrad η z) ≤
            X * Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
          have h1 : (u.toFun z + ε) ^ r * vecNormSq (parSpaceGrad η z) ≤
              (u.toFun z + ε) ^ r * (X * Q.indicator (fun _ => (1 : ℝ)) z) :=
            mul_le_mul_of_nonneg_left hX hvr
          refine h1.trans (le_of_eq ?_)
          by_cases hzq : z ∈ Q <;> simp [hzq]; ring
        nlinarith [hQ]
      have hnn1 : 0 ≤ η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) := by positivity
      have hnn2 : 0 ≤ Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
        by_cases hzq : z ∈ Q <;> simp [hzq, hvr]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by linarith [hc.hX]),
        ← ENNReal.ofReal_add (by positivity) (by have := hc.hX; positivity)]
      exact ENNReal.ofReal_le_ofReal hbd
    calc _ ≤ ∫⁻ z in U ×ˢ J, (ENNReal.ofReal (r ^ 2 / 2) * ENNReal.ofReal
              (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) +
            ENNReal.ofReal (2 * X) *
              ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z)) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (r ^ 2 / 2) * (∫⁻ z in U ×ˢ J, ENNReal.ofReal
              (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z))) +
          ENNReal.ofReal (2 * X) * (∫⁻ z in U ×ˢ J,
              ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z)) := by
          rw [lintegral_add_left' (hgm.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          exact (lintegral_mono_set (prod_mono subset_rfl hJI)).trans hPl
  have hmain := hGN hU hfin hJ hJI u G hG1 M hM0 hM η hc.smooth Kx hKx hKxU hηK S _ hS' hD
  refine le_trans (le_of_eq ?_) hmain
  refine lintegral_congr_ae ?_
  filter_upwards [hI0] with z hz
  obtain ⟨-, -, hGabs⟩ := hGv _ hz
  have hv : 0 < u.toFun z + ε := by linarith
  have hη0 := hc.nonneg z
  rw [abs_mul, abs_of_nonneg hη0, hGabs, ENNReal.ofReal_rpow_of_nonneg (by positivity)
    (by positivity)]
  rw [Real.mul_rpow hη0 (Real.rpow_nonneg hv.le _), ← Real.rpow_mul hv.le]
  congr 3
  ring

end PDE.Parabolic.WeakHarnack
