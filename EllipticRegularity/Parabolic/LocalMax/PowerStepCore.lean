module

public import EllipticRegularity.Parabolic.LocalMax.SliceSobolev
public import EllipticRegularity.Parabolic.Energy.Limits

/-!
# From the power energy estimate to the reverse Hölder step

Given the conclusions of the power energy estimate for a nonlinearity `F` (an almost-every-time
bound `∫ η²F(u)(t) ≤ R`, a gradient bound `∫∫ η²F''(u)|∇u|² ≤ 2R`, and the cutoff part
`∫∫ 2ΛK F(u)|∇η|² ≤ R` of `R`), and a companion `G` with `G² ≤ K F`, `G'² ≤ K F''` on `[0,∞)`,
the parabolic Sobolev step gives `∫∫ |η G(u)|^{2(d+2)/d} ≤ C(d) (K R)^{2/d} (5 K R)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set

/-- Pointwise gradient bound for `η G(u)`. -/
theorem vecNormSq_cutoffCompGrad_le {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (u : ParH1Function U I) {F G : ℝ → ℝ} {K : ℝ} (η : Vec d × ℝ → ℝ) (z : Vec d × ℝ)
    (hG : G (u.toFun z) ^ 2 ≤ K * F (u.toFun z))
    (hG' : deriv G (u.toFun z) ^ 2 ≤ K * deriv (deriv F) (u.toFun z)) :
    vecNormSq (cutoffCompGrad u G η z) ≤
      2 * K * (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) +
        2 * K * (F (u.toFun z) * vecNormSq (parSpaceGrad η z)) := by
  unfold cutoffCompGrad
  refine (vecNormSq_add_le _ _).trans ?_
  rw [vecNormSq_smul, vecNormSq_smul]
  have h1 := vecNormSq_nonneg (u.grad z)
  have h2 := vecNormSq_nonneg (parSpaceGrad η z)
  have hη := sq_nonneg (η z)
  have e1 : (deriv G (u.toFun z) * η z) ^ 2 * vecNormSq (u.grad z) =
      deriv G (u.toFun z) ^ 2 * (η z ^ 2 * vecNormSq (u.grad z)) := by ring
  have i1 : deriv G (u.toFun z) ^ 2 * (η z ^ 2 * vecNormSq (u.grad z)) ≤
      K * deriv (deriv F) (u.toFun z) * (η z ^ 2 * vecNormSq (u.grad z)) :=
    mul_le_mul_of_nonneg_right hG' (mul_nonneg hη h1)
  have i2 : G (u.toFun z) ^ 2 * vecNormSq (parSpaceGrad η z) ≤
      K * F (u.toFun z) * vecNormSq (parSpaceGrad η z) :=
    mul_le_mul_of_nonneg_right hG h2
  rw [e1]
  nlinarith [i1, i2]

/-- **Reverse Hölder core.** The constant depends only on the dimension. -/
theorem cutoff_comp_energy_sobolev (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {U : Set (Vec d)} {I J : Set ℝ}, IsOpen U → volume U ≠ ⊤ →
      MeasurableSet J → J ⊆ I → ∀ (u : ParH1Function U I),
      (∀ᵐ z ∂(volume.restrict (U ×ˢ J)), 0 ≤ u.toFun z) →
      ∀ (F G : ℝ → ℝ), ContDiff ℝ 1 G → ∀ M : ℝ, 0 ≤ M → (∀ s, |deriv G s| ≤ M) →
      ∀ {K Lam : ℝ}, 1 ≤ K → 1 ≤ Lam →
      (∀ s, 0 ≤ s → 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧ G s ^ 2 ≤ K * F s ∧
        deriv G s ^ 2 ≤ K * deriv (deriv F) s) →
      ∀ η : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → ∀ Kx : Set (Vec d), IsCompact Kx →
      Kx ⊆ U → (∀ x t, x ∉ Kx → η (x, t) = 0) → ∀ R : ℝ≥0∞,
      (∀ᵐ t ∂(volume.restrict J),
        ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) ≤ R) →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal
        (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) ≤ 2 * R →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal
        (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) ≤ R →
      ∫⁻ z in U ×ˢ J, ENNReal.ofReal |η z * G (u.toFun z)| ^ (2 * ((d : ℝ) + 2) / d) ≤
        C * (ENNReal.ofReal K * R) ^ (2 / (d : ℝ)) * (ENNReal.ofReal (5 * K) * R) := by
  obtain ⟨C, hC, hGN⟩ := slice_cutoff_comp_gagliardo_nirenberg d hd
  refine ⟨C, hC, ?_⟩
  intro U I J hU hfin hJ hJI u hpos F G hG M hM hGM K Lam hK hLam hstr η hη Kx hKx hKxU hηx R
    hE1 hE2 hE3
  have hK0 : 0 ≤ K := by linarith
  refine hGN hU hfin hJ hJI u G hG M hM hGM η hη Kx hKx hKxU hηx _ _ ?_ ?_
  · -- slice bound
    have hprod : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict J)), 0 ≤ u.toFun z := by
      rw [← Energy.volume_restrict_prod]; exact hpos
    filter_upwards [hE1, PDE.Parabolic.Energy.ae_ae_swap hprod] with t ht hpt
    calc ∫⁻ x in U, ENNReal.ofReal ((η (x, t) * G (u.toFun (x, t))) ^ 2)
        ≤ ∫⁻ x in U, ENNReal.ofReal K * ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with x hx
          rw [← ENNReal.ofReal_mul hK0]
          refine ENNReal.ofReal_le_ofReal ?_
          have := (hstr _ hx).2.2.1
          have hη2 := sq_nonneg (η (x, t))
          calc (η (x, t) * G (u.toFun (x, t))) ^ 2
              = η (x, t) ^ 2 * G (u.toFun (x, t)) ^ 2 := by ring
            _ ≤ η (x, t) ^ 2 * (K * F (u.toFun (x, t))) :=
                mul_le_mul_of_nonneg_left this hη2
            _ = K * (η (x, t) ^ 2 * F (u.toFun (x, t))) := by ring
      _ = ENNReal.ofReal K * ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * R := by gcongr
  · -- gradient bound
    have hpt : ∀ᵐ z ∂(volume.restrict (U ×ˢ J)),
        ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z)) ≤
          ENNReal.ofReal (2 * K) * ENNReal.ofReal
              (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) +
            ENNReal.ofReal (1 / Lam) * ENNReal.ofReal
              (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) := by
      filter_upwards [hpos] with z hz
      obtain ⟨hF0, hF20, hG2, hG'2⟩ := hstr _ hz
      have hb := vecNormSq_cutoffCompGrad_le u (F := F) η z hG2 hG'2
      have hA : 0 ≤ η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hF20) (vecNormSq_nonneg _)
      have hB : 0 ≤ F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z)) :=
        mul_nonneg hF0 (by have := vecNormSq_nonneg (parSpaceGrad η z); positivity)
      have hLam0 : 0 < Lam := by linarith
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (mul_nonneg (by positivity) hA) (mul_nonneg (by positivity) hB)]
      refine ENNReal.ofReal_le_ofReal (hb.trans (le_of_eq ?_))
      field_simp
    have hmeasA : AEMeasurable (fun z => ENNReal.ofReal (2 * K) * ENNReal.ofReal
        (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)))
        (volume.restrict (U ×ˢ J)) := by
      refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_).const_mul _
      have hμ : volume.restrict (U ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
        Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl
      have huM : AEMeasurable u.toFun (volume.restrict (U ×ˢ J)) :=
        (u.memL2.aestronglyMeasurable.mono_measure hμ).aemeasurable
      have hgM : AEMeasurable u.grad (volume.restrict (U ×ˢ J)) :=
        aemeasurable_pi_iff.2 fun i =>
          ((u.gradMemL2 i).aestronglyMeasurable.mono_measure hμ).aemeasurable
      have hηc : Continuous η := hη.continuous
      have hF2 : Measurable (deriv (deriv F)) := measurable_deriv _
      exact ((hηc.measurable.comp_aemeasurable aemeasurable_id).pow_const 2).mul
        (hF2.comp_aemeasurable huM) |>.mul (continuous_vecNormSq.measurable.comp_aemeasurable hgM)
    calc ∫⁻ z in U ×ˢ J, ENNReal.ofReal (vecNormSq (cutoffCompGrad u G η z))
        ≤ ∫⁻ z in U ×ˢ J, (ENNReal.ofReal (2 * K) * ENNReal.ofReal
              (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z)) +
            ENNReal.ofReal (1 / Lam) * ENNReal.ofReal
              (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z)))) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (2 * K) * (∫⁻ z in U ×ˢ J, ENNReal.ofReal
              (η z ^ 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z))) +
            ENNReal.ofReal (1 / Lam) * ∫⁻ z in U ×ˢ J, ENNReal.ofReal
              (F (u.toFun z) * (2 * Lam * K * vecNormSq (parSpaceGrad η z))) := by
          rw [lintegral_add_left' hmeasA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * K) * (2 * R) + ENNReal.ofReal (1 / Lam) * R := by gcongr
      _ = (ENNReal.ofReal (2 * K) * 2 + ENNReal.ofReal (1 / Lam)) * R := by ring
      _ ≤ ENNReal.ofReal (5 * K) * R := by
          gcongr
          have hL : 1 / Lam ≤ 1 := by rw [div_le_one (by linarith)]; exact hLam
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)

end PDE.Parabolic.LocalMax
