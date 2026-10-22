module

public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.OneDimNormalized

/-!
# One-dimensional Prékopa--Leindler for bounded functions

Rescaling the normalized case, together with the weighted AM-GM inequality in `[0,∞]`.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- Weighted AM-GM in `[0,∞]`. -/
theorem rpow_mul_rpow_le {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (u v : ℝ≥0∞) :
    u ^ l * v ^ (1 - l) ≤ ENNReal.ofReal l * u + ENNReal.ofReal (1 - l) * v := by
  have hl' : 0 < 1 - l := sub_pos.2 hl1
  rcases eq_or_ne u ∞ with rfl | hu
  · have : ENNReal.ofReal l * ∞ = ∞ := ENNReal.mul_top (by simpa using hl0)
    rw [this]; simp
  rcases eq_or_ne v ∞ with rfl | hv
  · have : ENNReal.ofReal (1 - l) * ∞ = ∞ := ENNReal.mul_top (by simpa using hl')
    rw [this]; simp
  lift u to NNReal using hu
  lift v to NNReal using hv
  have hu0 : (0 : ℝ) ≤ u := u.2
  have hv0 : (0 : ℝ) ≤ v := v.2
  have h := Real.geom_mean_le_arith_mean2_weighted hl0.le hl'.le hu0 hv0 (by ring)
  have h2 := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hu0 _),
    ENNReal.ofReal_add (mul_nonneg hl0.le hu0) (mul_nonneg hl'.le hv0),
    ENNReal.ofReal_mul hl0.le, ENNReal.ofReal_mul hl'.le,
    ← ENNReal.ofReal_rpow_of_nonneg hu0 hl0.le, ← ENNReal.ofReal_rpow_of_nonneg hv0 hl'.le,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h2
  exact h2

/-- One-dimensional Prékopa--Leindler for bounded measurable functions. -/
theorem oneDim_bounded {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g k : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    {M N : ℝ≥0∞} (hM : M ≠ ∞) (hN : N ≠ ∞) (hfM : ∀ x, f x ≤ M) (hgN : ∀ x, g x ≤ N)
    (hyp : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ k (l • x + (1 - l) • y)) :
    (∫⁻ x, f x) ^ l * (∫⁻ x, g x) ^ (1 - l) ≤ ∫⁻ x, k x := by
  have hl' : 0 < 1 - l := sub_pos.2 hl1
  set a := ⨆ x, f x with ha
  set b := ⨆ x, g x with hb
  have haM : a ≤ M := iSup_le hfM
  have hbN : b ≤ N := iSup_le hgN
  have ha_top : a ≠ ∞ := ne_top_of_le_ne_top hM haM
  have hb_top : b ≠ ∞ := ne_top_of_le_ne_top hN hbN
  by_cases ha0 : a = 0
  · have : ∀ x, f x = 0 := fun x => le_antisymm (ha0 ▸ le_iSup f x) bot_le
    simp [this, ENNReal.zero_rpow_of_pos hl0]
  by_cases hb0 : b = 0
  · have : ∀ x, g x = 0 := fun x => le_antisymm (hb0 ▸ le_iSup g x) bot_le
    simp [this, ENNReal.zero_rpow_of_pos hl']
  set ca := (a ^ l)⁻¹ with hca
  set cb := (b ^ (1 - l))⁻¹ with hcb
  have hal0 : a ^ l ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha_top).ne'
  have hbl0 : b ^ (1 - l) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hb_top).ne'
  have hca0 : ca ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.rpow_ne_top_of_nonneg hl0.le ha_top)
  have hcb0 : cb ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.rpow_ne_top_of_nonneg hl'.le hb_top)
  have hcat : ca ≠ ∞ := ENNReal.inv_ne_top.2 hal0
  have hcbt : cb ≠ ∞ := ENNReal.inv_ne_top.2 hbl0
  have hcc0 : ca * cb ≠ 0 := mul_ne_zero hca0 hcb0
  have hcct : ca * cb ≠ ∞ := ENNReal.mul_ne_top hcat hcbt
  have key := normalized_oneDim hl0 hl1 (f := fun x => a⁻¹ * f x) (g := fun x => b⁻¹ * g x)
    (k := fun x => (ca * cb) * k x) (hf.const_mul _) (hg.const_mul _) (hk.const_mul _)
    (fun x => by
      calc a⁻¹ * f x ≤ a⁻¹ * a := by gcongr; exact le_iSup f x
        _ = 1 := ENNReal.inv_mul_cancel ha0 ha_top)
    (fun x => by
      calc b⁻¹ * g x ≤ b⁻¹ * b := by gcongr; exact le_iSup g x
        _ = 1 := ENNReal.inv_mul_cancel hb0 hb_top)
    (fun t ht => by
      have h1 : a * t < a := by
        calc a * t < a * 1 := (ENNReal.mul_lt_mul_iff_right ha0 ha_top).2 ht
          _ = a := mul_one _
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 h1
      refine ⟨x, ?_⟩
      calc t = a⁻¹ * (a * t) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ha_top, one_mul]
        _ < a⁻¹ * f x := (ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.2 ha_top)
            (ENNReal.inv_ne_top.2 ha0)).2 hx)
    (fun t ht => by
      have h1 : b * t < b := by
        calc b * t < b * 1 := (ENNReal.mul_lt_mul_iff_right hb0 hb_top).2 ht
          _ = b := mul_one _
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 h1
      refine ⟨x, ?_⟩
      calc t = b⁻¹ * (b * t) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hb_top, one_mul]
        _ < b⁻¹ * g x := (ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.2 hb_top)
            (ENNReal.inv_ne_top.2 hb0)).2 hx)
    (fun x y => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hl0.le, ENNReal.mul_rpow_of_nonneg _ _ hl'.le,
        ENNReal.inv_rpow, ENNReal.inv_rpow]
      calc (a ^ l)⁻¹ * f x ^ l * ((b ^ (1 - l))⁻¹ * g y ^ (1 - l))
          = (ca * cb) * (f x ^ l * g y ^ (1 - l)) := by rw [hca, hcb]; ring
        _ ≤ (ca * cb) * k (l • x + (1 - l) • y) := by gcongr; exact hyp x y)
  rw [lintegral_const_mul _ hf, lintegral_const_mul _ hg, lintegral_const_mul _ hk] at key
  set F := ∫⁻ x, f x
  set G := ∫⁻ x, g x
  have amgm := rpow_mul_rpow_le hl0 hl1 (a⁻¹ * F) (b⁻¹ * G)
  have e : (a⁻¹ * F) ^ l * (b⁻¹ * G) ^ (1 - l) = (ca * cb) * (F ^ l * G ^ (1 - l)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hl0.le, ENNReal.mul_rpow_of_nonneg _ _ hl'.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, hca, hcb]; ring
  rw [e] at amgm
  exact (ENNReal.mul_le_mul_iff_right hcc0 hcct).1 (amgm.trans key)

end PDE.PrekopaLeindlerProof
