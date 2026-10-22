module

public import EllipticRegularity.DeGiorgi.MoserIter.SmallBounds
public import EllipticRegularity.DeGiorgi.MoserIter.AddConst
public import EllipticRegularity.DeGiorgi.MoserIter.DeltaLimit

/-!
# The second weak Harnack estimate (4.68)

The `δ`-reduction `u ↦ u + δ` and the two `p`-th power estimates of Step 3 of
Proposition 4.14, from the one-step estimate (H2b).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.DGNMMoser

/-- `∥u + δ∥_p^p ≤ ∥u∥_p^p + δ^p μ(X)` for `0 < p ≤ 1`. -/
theorem rpow_eLpNorm_add_const_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : α → ℝ} (hu : AEMeasurable u μ) {p δ : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ) :
    eLpNorm (fun x => u x + δ) (ENNReal.ofReal p) μ ^ p ≤
      eLpNorm u (ENNReal.ofReal p) μ ^ p + ENNReal.ofReal (δ ^ p) * μ Set.univ := by
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hform : ∀ {g : α → ℝ}, AEMeasurable g μ →
      eLpNorm g (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖g x‖ₑ ^ p ∂μ := fun {g} hg => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top
      hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  rw [hform (hu.add_const δ), hform hu]
  calc ∫⁻ x, ‖u x + δ‖ₑ ^ p ∂μ ≤ ∫⁻ x, (‖u x‖ₑ ^ p + ENNReal.ofReal (δ ^ p)) ∂μ := by
        refine lintegral_mono fun x => ?_
        calc ‖u x + δ‖ₑ ^ p ≤ (‖u x‖ₑ + ENNReal.ofReal δ) ^ p := by
              refine ENNReal.rpow_le_rpow ?_ hp0.le
              calc ‖u x + δ‖ₑ = ENNReal.ofReal |u x + δ| := Real.enorm_eq_ofReal_abs _
                _ ≤ ENNReal.ofReal |u x| + ENNReal.ofReal |δ| := by
                    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
                    exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
                _ = _ := by rw [Real.enorm_eq_ofReal_abs, abs_of_pos hδ]
          _ ≤ ‖u x‖ₑ ^ p + ENNReal.ofReal δ ^ p := ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1
          _ = _ := by rw [ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le]
    _ = ∫⁻ x, ‖u x‖ₑ ^ p ∂μ + ENNReal.ofReal (δ ^ p) * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]

/-- Generic `δ → 0` step for `p`-th power estimates. -/
theorem le_mul_of_forall_delta_rpow {S E W : ℝ≥0∞} {K p : ℝ} (hp : 0 < p) (hW : W ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → S ≤ ENNReal.ofReal K * (E + ENNReal.ofReal (δ ^ p) * W)) :
    S ≤ ENNReal.ofReal K * E := by
  refine le_mul_of_forall_delta hW fun δ' hδ' => ?_
  have := h (δ' ^ (1 / p)) (Real.rpow_pos_of_pos hδ' _)
  rwa [← Real.rpow_mul hδ'.le, one_div_mul_cancel hp.ne', Real.rpow_one] at this

theorem exists_weakHarnack0_small_constant (d : ℕ) (hd : 3 ≤ d)
    (hSmall : WeakHarnackSmallOneStepHyp d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ p q : ℝ, 0 < p → p ≤ q → q < 1 →
        (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p ∧
        ∀ m : ℕ, 1 ≤ m → p = q * ((d : ℝ) / (d - 2)) ^ (-(m : ℝ)) →
          (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
            ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) *
              (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p := by
  obtain ⟨C₁, hC₁, hstep⟩ := hSmall
  set c₁ : ℝ := max C₁ 1 with hc₁def
  have hc₁ : 1 ≤ c₁ := le_max_right _ _
  have hc₀ : 0 < c₁ := by linarith
  have hfin := isFiniteMeasure_volumeOn_ball d (r := 1) one_pos
  set μ : Measure (Vec d) := volumeOn (euclideanBall (0 : Vec d) 1) with hμ
  set V : ℝ := max 1 (volume (euclideanBall (0 : Vec d) 1)).toReal with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hVol : volume (euclideanBall (0 : Vec d) 1) ≤ ENNReal.ofReal V := by
    have hne := (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (R := 1) one_pos).volume_ne_top
    calc volume (euclideanBall (0 : Vec d) 1)
        = ENNReal.ofReal (volume (euclideanBall (0 : Vec d) 1)).toReal :=
          (ENNReal.ofReal_toReal hne).symm
      _ ≤ ENNReal.ofReal V := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  refine ⟨smallConst d c₁ V, smallConst_pos hd hc₁ hV, ?_⟩
  intro Λ a hm hell u hpos hsuper p q hp hpq hq
  have hΛ : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := by linarith
  have hu_meas : AEMeasurable u.toFun μ := u.memL2.aestronglyMeasurable.aemeasurable
  set W : ℝ≥0∞ := μ Set.univ with hW
  have hWtop : W ≠ ⊤ := measure_ne_top _ _
  have hle : volumeOn (euclideanBall (0 : Vec d) (1 / 2)) ≤ μ :=
    Measure.restrict_mono (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl
  set E : ℝ≥0∞ := eLpNorm u.toFun (ENNReal.ofReal p) μ ^ p with hE
  set X : ℝ := Λ * p ^ 2 / (1 - q) ^ 2 + 1 with hX
  have hX0 : 0 ≤ Λ * p ^ 2 / (1 - q) ^ 2 := by positivity
  set γ : ℝ := (d : ℝ) / (d - 2) with hγdef
  have hbound : ∀ δ : ℝ, 0 < δ →
      (eLpNorm u.toFun (ENNReal.ofReal (q * γ))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
        ENNReal.ofReal (smallConst d c₁ V * X ^ (((d : ℝ) + 2) / 2)) *
          (E + ENNReal.ofReal (δ ^ p) * W) ∧
      ∀ m : ℕ, p * γ ^ m = q →
        (eLpNorm u.toFun (ENNReal.ofReal (q * γ))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
        ENNReal.ofReal (smallConst d c₁ V * X ^ ((d : ℝ) / 2)) *
          (E + ENNReal.ofReal (δ ^ p) * W) := by
    intro δ hδ
    set v : H1Function (euclideanBall (0 : Vec d) 1) := u.addConst δ with hvdef
    have hv : ∀ x, v.toFun x = u.toFun x + δ := fun x => rfl
    have hvsuper : IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) v :=
      superharmonic_addConst hsuper δ
    have hδv : ∀ᵐ x ∂μ, δ ≤ v.toFun x := by
      filter_upwards [hpos] with x hx
      rw [hv]; linarith
    have hstep' : SmallStep v.toFun c₁ Λ := by
      intro p' hp'0 hp'1 r s h1 h2 h3
      refine (hstep Λ a hm hell v hvsuper δ hδ hδv p' hp'0 hp'1 r s h1 h2 h3).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_
        (by positivity))) le_rfl
      have hsr : 0 < s - r := by linarith
      have hX' : 0 ≤ Λ * p' ^ 2 / (1 - p') ^ 2 + 1 := by positivity
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _)
        (by positivity)) hX'
    have hv_meas : AEMeasurable v.toFun μ := v.memL2.aestronglyMeasurable.aemeasurable
    have hsb := small_bounds hd hv_meas hc₁ hΛ0.le hV hVol hstep' hp hpq hq
    have hSle : (eLpNorm u.toFun (ENNReal.ofReal (q * γ))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
        (eLpNorm v.toFun (ENNReal.ofReal (q * γ))
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p := by
      refine ENNReal.rpow_le_rpow ?_ hp.le
      refine eLpNorm_mono_ae (u.memL2.aestronglyMeasurable.mono_measure hle) ?_
      have : ∀ᵐ x ∂μ, ‖u.toFun x‖ ≤ ‖v.toFun x‖ := by
        filter_upwards [hpos] with x hx
        rw [Real.norm_of_nonneg hx.le, Real.norm_of_nonneg (by rw [hv]; linarith), hv]
        linarith
      exact ae_mono hle this
    have hEv : eLpNorm v.toFun (ENNReal.ofReal p) μ ^ p ≤ E + ENNReal.ofReal (δ ^ p) * W :=
      rpow_eLpNorm_add_const_le hu_meas hp (by linarith) hδ
    exact ⟨hSle.trans (hsb.1.trans (mul_le_mul' le_rfl hEv)),
      fun m hm => hSle.trans ((hsb.2 m hm).trans (mul_le_mul' le_rfl hEv))⟩
  have hqd : q * (d : ℝ) / (d - 2) = q * γ := mul_div_assoc _ _ _
  rw [hqd]
  refine ⟨le_mul_of_forall_delta_rpow hp hWtop fun δ hδ => (hbound δ hδ).1, ?_⟩
  intro m _ hpm
  refine le_mul_of_forall_delta_rpow hp hWtop fun δ hδ => (hbound δ hδ).2 m ?_
  rw [hpm, Real.rpow_neg (by have := one_lt_gamma hd; linarith), Real.rpow_natCast]
  have : 0 < γ ^ m := pow_pos (by have := one_lt_gamma hd; linarith) m
  field_simp

end PDE.DGNMMoser
