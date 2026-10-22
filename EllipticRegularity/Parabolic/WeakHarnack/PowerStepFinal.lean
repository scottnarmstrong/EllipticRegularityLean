/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerStepGeneral

/-! # The power step on the weak Harnack cylinder families

Specializations of `posStep_general` / `negStep_general` to the families `posCyl`, `negCyl`,
`negCylInner` of `Geometry.lean`, in exactly the form of the hypotheses `H1step`, `H2neg`,
`H2inner` of `weakHarnack_of_steps`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

/-- Real bookkeeping: the constant for a gap `g ≥ δ/κ`. -/
theorem step_const_le {W C g δ κ A : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hg : δ / κ ≤ g) (hδ : 0 < δ)
    (hκ : 0 < κ) (hA : W * κ ^ 2 * C ≤ A) : W * (C / g ^ 2) ≤ A * δ ^ (-(2 : ℝ)) := by
  have hg0 : 0 < δ / κ := by positivity
  have h1 : (δ / κ) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hg0.le hg 2
  have h2 : C / g ^ 2 ≤ C / (δ / κ) ^ 2 :=
    div_le_div_of_nonneg_left hC (by positivity) h1
  have h3 : C / (δ / κ) ^ 2 = C * κ ^ 2 / δ ^ 2 := by field_simp
  have h4 : δ ^ (-(2 : ℝ)) = 1 / δ ^ 2 := by
    rw [Real.rpow_neg hδ.le, Real.rpow_two]; simp
  rw [h4]
  calc W * (C / g ^ 2) ≤ W * (C * κ ^ 2 / δ ^ 2) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hW
    _ = (W * κ ^ 2 * C) / δ ^ 2 := by ring
    _ ≤ A / δ ^ 2 := div_le_div_of_nonneg_right hA (by positivity)
    _ = A * (1 / δ ^ 2) := by ring


/-- Constant conversion from `ofReal (base ^ (1/p))` bounds. -/
theorem ofReal_rpow_mono {a b p : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal (a ^ (1 / p)) ≤ ENNReal.ofReal (b ^ (1 / p)) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha hab (by positivity))

/-- **Positive power step on `posCyl`** (hypothesis `H1step` of `weakHarnack_of_steps`). -/
theorem parabPowerStepPos (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ A m : ℝ, 1 ≤ A ∧ 0 < m ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ q →
        eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
            ((cylMeasure (posCyl d 1)).restrict (posCyl d σ')) ≤
          ENNReal.ofReal ((A * (σ - σ') ^ (-m)) ^ (1 / p)) *
            eLpNorm (fun z => u.toFun z + ε) (ENNReal.ofReal p)
              ((cylMeasure (posCyl d 1)).restrict (posCyl d σ)) := by
  obtain ⟨C, hC1, hC⟩ := posStep_general d hd Lam (by linarith) q hq0 hq1
  set Vr : ℝ := (volume (posCyl d 1)).toReal with hVr
  set W : ℝ := (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) * Vr with hW
  have hW0 : 0 ≤ W := by
    have : 0 ≤ Vr := ENNReal.toReal_nonneg
    positivity
  set A : ℝ := max 1 (W * 4 ^ 2 * C) with hA
  refine ⟨A, 2, le_max_left _ _, by norm_num, ?_⟩
  intro a ha u hu hu0 ε hε σ' σ hσ' hσσ' hσ1 p hp hpq
  have hgap : 0 < σ - σ' := by linarith
  have hS0 : volume (posCyl d 1) ≠ 0 := (volume_posCyl_pos (by norm_num)).ne'
  have hSt : volume (posCyl d 1) ≠ ⊤ := volume_posCyl_ne_top (by norm_num)
  have hres := hC a ha u hu hu0 ε hε (S₁ := posCyl d 1) hS0 hSt
    (r' := posR σ') (ρ := posR σ) (s := posLo σ) (s' := posLo σ') (t' := posHi σ')
    (t := posHi σ) (by unfold posR; linarith) (by unfold posR; linarith)
    (by unfold posR; linarith) (by unfold posLo; linarith) (by unfold posLo; linarith)
    (by unfold posLo posHi; linarith) (by unfold posHi; linarith) (by unfold posHi; linarith)
    (by rw [← posCyl_eq]; exact posCyl_mono (by linarith) hσ1) p hp hpq
  have hmin : (σ - σ') / 4 ≤ min (posR σ - posR σ') (min (posLo σ' - posLo σ) (posHi σ - posHi σ')) := by
    rw [posR_sub, posLo_sub, posHi_sub]
    refine le_min (by linarith) (le_min le_rfl le_rfl)
  have hC0 : 0 ≤ C := by linarith
  have hbase := step_const_le hW0 hC0 hmin hgap (by norm_num : (0 : ℝ) < 4)
    (A := A) (le_max_right _ _)
  have hbase' : (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
      (C / (min (posR σ - posR σ') (min (posLo σ' - posLo σ) (posHi σ - posHi σ'))) ^ 2) * Vr ≤
      A * (σ - σ') ^ (-(2 : ℝ)) := by
    have := hbase
    rw [hW] at this
    linarith [this, show (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) * Vr * (C / (min (posR σ - posR σ')
      (min (posLo σ' - posLo σ) (posHi σ - posHi σ'))) ^ 2) = (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
      (C / (min (posR σ - posR σ') (min (posLo σ' - posLo σ) (posHi σ - posHi σ'))) ^ 2) * Vr by
      ring]
  refine hres.trans (mul_le_mul' ?_ le_rfl)
  refine ofReal_rpow_mono hp (by
    have : 0 ≤ Vr := ENNReal.toReal_nonneg
    have hg0 : 0 < min (posR σ - posR σ') (min (posLo σ' - posLo σ) (posHi σ - posHi σ')) :=
      lt_of_lt_of_le (by linarith) hmin
    positivity) hbase'


/-- **Negative power step on `negCyl`** (hypothesis `H2neg` of `weakHarnack_of_steps`). -/
theorem parabPowerStepNeg (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ A β m : ℝ, 1 ≤ A ∧ 0 ≤ β ∧ 0 < m ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
        eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
            ((cylMeasure (negCyl d 1)).restrict (negCyl d σ')) ≤
          ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
            eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal p)
              ((cylMeasure (negCyl d 1)).restrict (negCyl d σ)) := by
  obtain ⟨C, hC1, hC⟩ := negStep_general d hd Lam (by linarith)
  set Vr : ℝ := (volume (negCyl d 1)).toReal with hVr
  set W : ℝ := (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) * Vr with hW
  have hW0 : 0 ≤ W := by
    have : 0 ≤ Vr := ENNReal.toReal_nonneg
    positivity
  set A : ℝ := max 1 (W * 16 ^ 2 * C) with hA
  refine ⟨A, 0, 2, le_max_left _ _, le_rfl, by norm_num, ?_⟩
  intro a ha u hu hu0 ε hε σ' σ hσ' hσσ' hσ1 p hp
  have hgap : 0 < σ - σ' := by linarith
  have hS0 : volume (negCyl d 1) ≠ 0 := (volume_negCyl_pos (by norm_num)).ne'
  have hSt : volume (negCyl d 1) ≠ ⊤ := volume_negCyl_ne_top (by norm_num)
  have hres := hC a ha u hu hu0 ε hε (S₁ := negCyl d 1) hS0 hSt
    (r' := negR σ') (ρ := negR σ) (s := negLo σ) (s' := negLo σ')
    (by unfold negR; linarith) (by unfold negR; linarith)
    (by unfold negR; linarith) (by unfold negLo; linarith) (by unfold negLo; linarith)
    (by unfold negLo; linarith)
    (by rw [← negCyl_eq]; exact negCyl_mono (by linarith) hσ1) p hp
  have hmin : (σ - σ') / 16 ≤ min (negR σ - negR σ') (negLo σ' - negLo σ) := by
    rw [negR_sub, negLo_sub]
    exact le_min (by linarith) le_rfl
  have hC0 : 0 ≤ C := by linarith
  have hbase := step_const_le hW0 hC0 hmin hgap (by norm_num : (0 : ℝ) < 16)
    (A := A) (le_max_right _ _)
  have hbase' : (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
      (C / (min (negR σ - negR σ') (negLo σ' - negLo σ)) ^ 2) * Vr ≤
      A * (1 + p) ^ (0 : ℝ) * (σ - σ') ^ (-(2 : ℝ)) := by
    rw [Real.rpow_zero, mul_one]
    have := hbase
    rw [hW] at this
    linarith [this, show (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) * Vr * (C / (min (negR σ - negR σ')
      (negLo σ' - negLo σ)) ^ 2) = (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
      (C / (min (negR σ - negR σ') (negLo σ' - negLo σ)) ^ 2) * Vr by ring]
  refine hres.trans (mul_le_mul' ?_ le_rfl)
  refine ofReal_rpow_mono hp (by
    have : 0 ≤ Vr := ENNReal.toReal_nonneg
    have hg0 : 0 < min (negR σ - negR σ') (negLo σ' - negLo σ) :=
      lt_of_lt_of_le (by linarith) hmin
    positivity) hbase'

/-- **Negative power step on `negCylInner`** (hypothesis `H2inner` of `weakHarnack_of_steps`). -/
theorem parabPowerStepNegInner (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ A β m : ℝ, 1 ≤ A ∧ 0 ≤ β ∧ 0 < m ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
        eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal ((1 + 2 / (d : ℝ)) * p))
            ((cylMeasure (negCylInner d 1)).restrict (negCylInner d σ')) ≤
          ENNReal.ofReal ((A * (1 + p) ^ β * (σ - σ') ^ (-m)) ^ (1 / p)) *
            eLpNorm (fun z => 1 / (u.toFun z + ε)) (ENNReal.ofReal p)
              ((cylMeasure (negCylInner d 1)).restrict (negCylInner d σ)) := by
  obtain ⟨C, hC1, hC⟩ := negStep_general d hd Lam (by linarith)
  set Vr : ℝ := (volume (negCylInner d 1)).toReal with hVr
  set W : ℝ := (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) * Vr with hW
  have hW0 : 0 ≤ W := by
    have : 0 ≤ Vr := ENNReal.toReal_nonneg
    positivity
  set A : ℝ := max 1 (W * 8 ^ 2 * C) with hA
  refine ⟨A, 0, 2, le_max_left _ _, le_rfl, by norm_num, ?_⟩
  intro a ha u hu hu0 ε hε σ' σ hσ' hσσ' hσ1 p hp
  have hgap : 0 < σ - σ' := by linarith
  have hS0 : volume (negCylInner d 1) ≠ 0 := (volume_negCylInner_pos (by norm_num)).ne'
  have hSt : volume (negCylInner d 1) ≠ ⊤ := volume_negCylInner_ne_top (by norm_num)
  have hres := hC a ha u hu hu0 ε hε (S₁ := negCylInner d 1) hS0 hSt
    (r' := innR σ') (ρ := innR σ) (s := innLo σ) (s' := innLo σ')
    (by unfold innR; linarith) (by unfold innR; linarith)
    (by unfold innR; linarith) (by unfold innLo; linarith) (by unfold innLo; linarith)
    (by unfold innLo; linarith)
    (by rw [← negCylInner_eq]; exact negCylInner_mono (by linarith) hσ1) p hp
  have hmin : (σ - σ') / 8 ≤ min (innR σ - innR σ') (innLo σ' - innLo σ) := by
    rw [innR_sub, innLo_sub]
    exact le_min (by linarith) le_rfl
  have hC0 : 0 ≤ C := by linarith
  have hbase := step_const_le hW0 hC0 hmin hgap (by norm_num : (0 : ℝ) < 8)
    (A := A) (le_max_right _ _)
  have hbase' : (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
      (C / (min (innR σ - innR σ') (innLo σ' - innLo σ)) ^ 2) * Vr ≤
      A * (1 + p) ^ (0 : ℝ) * (σ - σ') ^ (-(2 : ℝ)) := by
    rw [Real.rpow_zero, mul_one]
    have := hbase
    rw [hW] at this
    linarith [this, show (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) * Vr * (C / (min (innR σ - innR σ')
      (innLo σ' - innLo σ)) ^ 2) = (Vr⁻¹) ^ (1 / (1 + 2 / (d : ℝ))) *
      (C / (min (innR σ - innR σ') (innLo σ' - innLo σ)) ^ 2) * Vr by ring]
  refine hres.trans (mul_le_mul' ?_ le_rfl)
  refine ofReal_rpow_mono hp (by
    have : 0 ≤ Vr := ENNReal.toReal_nonneg
    have hg0 : 0 < min (innR σ - innR σ') (innLo σ' - innLo σ) :=
      lt_of_lt_of_le (by linarith) hmin
    positivity) hbase'

end PDE.Parabolic.WeakHarnack
