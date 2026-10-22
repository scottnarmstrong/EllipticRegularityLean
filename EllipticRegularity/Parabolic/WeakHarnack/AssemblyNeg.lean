module

public import EllipticRegularity.Parabolic.WeakHarnack.AssemblyScale

/-!
# Negative side: Bombieri-Giusti for `e^k / v` and the Moser iteration to `L^∞`

For `v ≥ ε > 0`: from the negative power steps on `negCyl` and `negCylInner` and the
logarithmic tail for `e^k / v` we bound `‖1/v‖_{L^∞(Q⁺)} ≤ C e^{-k}` (normalized w.r.t.
`cylMeasure (negCyl d 1)`), with `C` independent of `v` and `k`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

/-- The constant of the `L^∞` bound for `1/v`. -/
noncomputable def negTopConst (d : ℕ) (χ A β m A₃ β₃ m₃ c₀ : ℝ) : ℝ :=
  PDE.ParabIter.linC χ A₃ β₃ m₃ * (1 - 1 / 2 : ℝ) ^ (-PDE.ParabIter.linM χ m₃) *
    (negRatio d).toReal *
    PDE.Bombieri.giustiConst (1 / 2) 1 (max c₀ (PDE.ParabIter.negC χ A β m))
      (PDE.ParabIter.negM χ m)

theorem linC_pos' {χ A₃ β₃ m₃ : ℝ} (hχ : 1 < χ) (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃)
    (hm₃ : 0 < m₃) : 0 < PDE.ParabIter.linC χ A₃ β₃ m₃ := by
  have hχ0 : 0 < χ := by linarith
  have h2 : (1 : ℝ) ≤ A₃ * 2 ^ β₃ * 2 ^ m₃ := by
    have h1 : (1 : ℝ) ≤ 2 ^ β₃ := Real.one_le_rpow (by norm_num) hβ₃
    have h3 : (1 : ℝ) ≤ 2 ^ m₃ := Real.one_le_rpow (by norm_num) hm₃.le
    have : 1 ≤ A₃ * 2 ^ β₃ := one_le_mul_of_one_le_of_one_le hA₃ h1
    exact one_le_mul_of_one_le_of_one_le this h3
  unfold PDE.ParabIter.linC
  have hb : (0 : ℝ) < χ ^ β₃ * 2 ^ m₃ := by positivity
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hb _)

theorem negTopConst_pos (d : ℕ) {χ A β m A₃ β₃ m₃ c₀ : ℝ} (hχ : 1 < χ) (hA₃ : 1 ≤ A₃)
    (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) : 0 < negTopConst d χ A β m A₃ β₃ m₃ c₀ := by
  have hlin := linC_pos' hχ hA₃ hβ₃ hm₃
  have hrat : 0 < (negRatio d).toReal := ENNReal.toReal_pos negRatio_ne_zero negRatio_ne_top
  unfold negTopConst
  have := PDE.Bombieri.giustiConst_pos (1 / 2) 1 (max c₀ (PDE.ParabIter.negC χ A β m))
    (PDE.ParabIter.negM χ m)
  have h5 : (0 : ℝ) < (1 - 1 / 2 : ℝ) ^ (-PDE.ParabIter.linM χ m₃) :=
    Real.rpow_pos_of_pos (by norm_num) _
  positivity

theorem neg_side {χ A β m A₃ β₃ m₃ k c₀ ε : ℝ} (hχ : 1 < χ) (hA : 1 ≤ A) (hβ : 0 ≤ β)
    (hm : 0 < m) (hA₃ : 1 ≤ A₃) (hβ₃ : 0 ≤ β₃) (hm₃ : 0 < m₃) (hε : 0 < ε)
    {v : Vec d × ℝ → ℝ} (hv : Measurable v) (hvε : ∀ z, ε ≤ v z)
    (hstep : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / v z) (ENNReal.ofReal (χ * p))
          ((cylMeasure (negCyl d 1)).restrict (negCyl d σ')) ≤
        ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm (fun z => 1 / v z) (ENNReal.ofReal p)
            ((cylMeasure (negCyl d 1)).restrict (negCyl d σ)))
    (hstep₃ : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / v z) (ENNReal.ofReal (χ * p))
          ((cylMeasure (negCylInner d 1)).restrict (negCylInner d σ')) ≤
        ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
          eLpNorm (fun z => 1 / v z) (ENNReal.ofReal p)
            ((cylMeasure (negCylInner d 1)).restrict (negCylInner d σ)))
    (hlog : ∀ lam : ℝ, 0 < lam →
      cylMeasure (negCyl d 1) (negCyl d 1 ∩ {z | lam < Real.log (Real.exp k / v z)}) ≤
        ENNReal.ofReal (c₀ / lam)) :
    eLpNorm (fun z => 1 / v z) ⊤ ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))) ≤
      ENNReal.ofReal (negTopConst d χ A β m A₃ β₃ m₃ c₀ * Real.exp (-k)) := by
  have hvpos : ∀ z, 0 < v z := fun z => hε.trans_le (hvε z)
  have hg : Measurable (fun z => 1 / v z) := by fun_prop
  have hgpos : ∀ z, 0 < 1 / v z := fun z => one_div_pos.2 (hvpos z)
  -- Bombieri-Giusti for `e^k / v` on `negCyl`
  obtain ⟨hc1, hM, hrh⟩ := PDE.ParabIter.hrh_of_negStep (cylMeasure (negCyl d 1)) (negCyl d)
    (fun z => 1 / v z) (δ := 1 / 2) (by norm_num) hχ hA hβ hm negCyl_hUmono hstep
  have hc : 1 ≤ max c₀ (PDE.ParabIter.negC χ A β m) := hc1.trans (le_max_right _ _)
  have hrh' := hrh_mono_const (1 / 2) 1 (PDE.ParabIter.negM χ m) one_pos
    (cylMeasure (negCyl d 1)) (negCyl d) (fun z => 1 / v z) (by linarith) (le_max_right c₀ _) hrh
  have hek : 0 ≤ Real.exp k := (Real.exp_pos _).le
  set f : Vec d × ℝ → ℝ := fun z => Real.exp k / v z with hf
  have hfeq : f = fun z => Real.exp k * (1 / v z) := by
    funext z; simp only [hf, mul_one_div]
  have hrhf : ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ α : ℝ, 0 < α → α ≤ min 1 (1 / 2) →
      eLpNorm f (ENNReal.ofReal 1) ((cylMeasure (negCyl d 1)).restrict (negCyl d σ')) ≤
        ENNReal.ofReal ((max c₀ (PDE.ParabIter.negC χ A β m) * (σ - σ') ^
            (-PDE.ParabIter.negM χ m)) ^ (1 / α - 1 / 1)) *
          eLpNorm f (ENNReal.ofReal α) ((cylMeasure (negCyl d 1)).restrict (negCyl d σ)) := by
    intro σ' σ h1 h2 h3 α hα hαle
    rw [hfeq]
    exact step_const_mul hek (hrh' σ' σ h1 h2 h3 α hα hαle)
  have hfpos : ∀ z, 0 < f z := fun z => div_pos (Real.exp_pos _) (hvpos z)
  have hfin : eLpNorm f (ENNReal.ofReal 1) ((cylMeasure (negCyl d 1)).restrict (negCyl d 1)) < ⊤ := by
    have hbd : ∀ᵐ z ∂((cylMeasure (negCyl d 1)).restrict (negCyl d 1)), ‖f z‖ ≤ Real.exp k / ε := by
      refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_pos (hfpos z)]
      exact div_le_div_of_nonneg_left hek hε (hvε z)
    have hfm : Measurable f := measurable_const.div hv
    refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound hfm.aestronglyMeasurable hbd) ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (measure_ne_top _ _))
      ENNReal.ofReal_lt_top
  have hlogf : ∀ lam : ℝ, 0 < lam →
      cylMeasure (negCyl d 1) (negCyl d 1 ∩ {x | lam < Real.log (f x)}) ≤
        ENNReal.ofReal (max c₀ (PDE.ParabIter.negC χ A β m) / lam) := fun lam hlam =>
    (hlog lam hlam).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  have hB := PDE.Bombieri.bombieri_giusti (1 / 2) 1 (max c₀ (PDE.ParabIter.negC χ A β m))
    (PDE.ParabIter.negM χ m) (by norm_num) (by norm_num) one_pos hc hM
    (cylMeasure (negCyl d 1)) (negCyl d) negCyl_hUm negCyl_hUmono f (measurable_const.div hv)
    hfpos hfin hlogf hrhf
  -- `L^1` bound for `1/v`
  have hL1 : eLpNorm (fun z => 1 / v z) (ENNReal.ofReal 1)
      ((cylMeasure (negCyl d 1)).restrict (negCyl d (1 / 2))) ≤
      ENNReal.ofReal (PDE.Bombieri.giustiConst (1 / 2) 1
        (max c₀ (PDE.ParabIter.negC χ A β m)) (PDE.ParabIter.negM χ m) * Real.exp (-k)) := by
    have hge : (fun z => 1 / v z) = fun z => Real.exp (-k) * f z := by
      funext z
      simp only [hf]
      rw [← mul_div_assoc, ← Real.exp_add]
      simp
    rw [hge, eLpNorm_const_mul_fun f (Real.exp_pos _).le]
    calc ENNReal.ofReal (Real.exp (-k)) * eLpNorm f (ENNReal.ofReal 1)
          ((cylMeasure (negCyl d 1)).restrict (negCyl d (1 / 2)))
        ≤ ENNReal.ofReal (Real.exp (-k)) * ENNReal.ofReal (PDE.Bombieri.giustiConst (1 / 2) 1
          (max c₀ (PDE.ParabIter.negC χ A β m)) (PDE.ParabIter.negM χ m)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  -- Moser iteration on `negCylInner`
  have hLinf := PDE.ParabIter.linfty_of_negStep (cylMeasure (negCylInner d 1)) (negCylInner d)
    (fun z => 1 / v z) hg hgpos (δ := 1 / 2) (by norm_num) (by norm_num) hχ hA₃ hβ₃ hm₃
    negCylInner_hUmono hstep₃
  -- change of normalization
  have hsub1 : negCylInner d (1 / 2) ⊆ negCyl d 1 :=
    (negCylInner_mono (by norm_num) (by norm_num)).trans
      ((negCylInner_one (d := d)).subset.trans (negCyl_mono (by norm_num) (by norm_num)))
  have hsub2 : negCylInner d (1 / 2) ⊆ negCylInner d 1 := negCylInner_mono (by norm_num) (by norm_num)
  have hsub3 : negCylInner d 1 ⊆ negCyl d 1 :=
    (negCylInner_one (d := d)).subset.trans (negCyl_mono (by norm_num) (by norm_num))
  have hrat1 : (cylMeasure (negCylInner d 1)).restrict (negCylInner d (1 / 2)) =
      negRatio d • (cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2)) :=
    cylMeasure_restrict_ratio (measurableSet_negCylInner _) hsub1 hsub2
      (volume_negCyl_pos (by norm_num)).ne' (volume_negCyl_ne_top (by norm_num))
  have hrat2 : (cylMeasure (negCylInner d 1)).restrict (negCylInner d 1) =
      negRatio d • (cylMeasure (negCyl d 1)).restrict (negCylInner d 1) :=
    cylMeasure_restrict_ratio (measurableSet_negCylInner _) hsub3 subset_rfl
      (volume_negCyl_pos (by norm_num)).ne' (volume_negCyl_ne_top (by norm_num))
  have e1 : eLpNorm (fun z => 1 / v z) ⊤
      ((cylMeasure (negCylInner d 1)).restrict (negCylInner d (1 / 2))) =
      eLpNorm (fun z => 1 / v z) ⊤ ((cylMeasure (negCyl d 1)).restrict (negCylInner d (1 / 2))) := by
    rw [hrat1, eLpNorm_smul_measure_of_ne_zero negRatio_ne_zero]
    simp
  have e2 : eLpNorm (fun z => 1 / v z) (ENNReal.ofReal 1)
      ((cylMeasure (negCylInner d 1)).restrict (negCylInner d 1)) =
      negRatio d * eLpNorm (fun z => 1 / v z) (ENNReal.ofReal 1)
        ((cylMeasure (negCyl d 1)).restrict (negCyl d (1 / 2))) := by
    rw [hrat2, eLpNorm_smul_measure_of_ne_zero negRatio_ne_zero, ← negCylInner_one]
    simp
  rw [e1, e2] at hLinf
  refine hLinf.trans ?_
  have hR : negRatio d = ENNReal.ofReal (negRatio d).toReal :=
    (ENNReal.ofReal_toReal negRatio_ne_top).symm
  have hlinpos : 0 ≤ PDE.ParabIter.linC χ A₃ β₃ m₃ * (1 - 1 / 2 : ℝ) ^ (-PDE.ParabIter.linM χ m₃) :=
    mul_nonneg (linC_pos' hχ hA₃ hβ₃ hm₃).le (Real.rpow_nonneg (by norm_num) _)
  calc ENNReal.ofReal (PDE.ParabIter.linC χ A₃ β₃ m₃ * (1 - 1 / 2 : ℝ) ^ (-PDE.ParabIter.linM χ m₃)) *
        (negRatio d * eLpNorm (fun z => 1 / v z) (ENNReal.ofReal 1)
          ((cylMeasure (negCyl d 1)).restrict (negCyl d (1 / 2))))
      ≤ ENNReal.ofReal (PDE.ParabIter.linC χ A₃ β₃ m₃ * (1 - 1 / 2 : ℝ) ^ (-PDE.ParabIter.linM χ m₃)) *
        (ENNReal.ofReal (negRatio d).toReal * ENNReal.ofReal (PDE.Bombieri.giustiConst (1 / 2) 1
          (max c₀ (PDE.ParabIter.negC χ A β m)) (PDE.ParabIter.negM χ m) * Real.exp (-k))) := by
        rw [← hR]; gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hlinpos]
        congr 1
        unfold negTopConst
        ring

end PDE.Parabolic.WeakHarnack
