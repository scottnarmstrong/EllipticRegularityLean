module

public import PDEFoundation.Euler.OsgoodGlobal

/-!
# Osgood vanishing from an almost-everywhere integral inequality

If `y ≥ 0`, `y ≤ B²` a.e., `y t ≤ -2 ∫_{[0,t]} Λ` for a.e. `t`, and `|Λ s| ≤ c p B^(2/p) y(s)^(1-1/p)`
for a.e. `s` and all `p ≥ 2`, then `y = 0` a.e. on `[0, T]`. The comparison function is
`min (2 ∫₀ᵗ |Λ|) B²`, which is continuous and dominates `y` a.e.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

theorem ae_eq_zero_of_integral_bound {y Λ : ℝ → ℝ} {T B c : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hΛ : IntegrableOn Λ (Icc 0 T)) (hy0 : ∀ t, 0 ≤ y t)
    (hyB : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), y t ≤ B ^ 2)
    (hyΛ : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), y t ≤ -2 * ∫ s in Icc (0 : ℝ) t, Λ s)
    (hΛy : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ p : ℝ, 2 ≤ p →
      |Λ s| ≤ c * p * B ^ (2 / p) * y s ^ (1 - 1 / p)) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), y t = 0 := by
  have hii : IntervalIntegrable (fun s => |Λ s|) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact hΛ.norm
  have hsub : ∀ t ∈ Icc (0 : ℝ) T, uIcc 0 t ⊆ uIcc 0 T := fun t ht =>
    Set.uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hT]; exact ht)
  set Z : ℝ → ℝ := fun t => 2 * ∫ s in (0 : ℝ)..t, |Λ s| with hZ
  set y' : ℝ → ℝ := fun t => min (Z t) (B ^ 2) with hy'
  have hZc : ContinuousOn Z (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hii (a := 0)
      left_mem_uIcc
    rw [uIcc_of_le hT] at this
    exact continuousOn_const.mul this
  have hy'c : ContinuousOn y' (Icc 0 T) := (continuous_id.min continuous_const).comp_continuousOn hZc
  have hZ0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Z t := fun t ht =>
    mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg ht.1 fun _ _ => abs_nonneg _)
  have hy'0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y' t := fun t ht =>
    le_min (hZ0 t ht) (sq_nonneg B)
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), t ∈ Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  -- `y ≤ y'` a.e.
  have hyy : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), y t ≤ y' t := by
    filter_upwards [hyB, hyΛ, hmem] with t h1 h2 ht
    refine le_min (h2.trans ?_) h1
    have e : ∫ s in Icc (0 : ℝ) t, Λ s = ∫ s in (0 : ℝ)..t, Λ s := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    have h3 : -(∫ s in Icc (0 : ℝ) t, Λ s) ≤ ∫ s in Icc (0 : ℝ) t, |Λ s| := by
      have := norm_integral_le_integral_norm (μ := volume.restrict (Icc (0 : ℝ) t)) Λ
      simp only [Real.norm_eq_abs] at this
      exact (neg_le_abs _).trans this
    have e2 : ∫ s in Icc (0 : ℝ) t, |Λ s| = ∫ s in (0 : ℝ)..t, |Λ s| := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    rw [e2] at h3
    simp only [hZ]
    linarith
  -- integral inequality for `y'`
  have hmain : ∀ p : ℝ, 2 ≤ p → ∀ t ∈ Icc (0 : ℝ) T,
      y' t ≤ ∫ τ in (0 : ℝ)..t, (2 * c) * p * B ^ (2 / p) * y' τ ^ (1 - 1 / p) := by
    intro p hp t ht
    have hp0 : 0 < p := by linarith
    have he : 0 ≤ 1 - 1 / p := by
      have : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
      linarith
    have hae : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
        2 * |Λ s| ≤ (2 * c) * p * B ^ (2 / p) * y' s ^ (1 - 1 / p) := by
      filter_upwards [hΛy, hyy] with s h1 h2
      have h3 : y s ^ (1 - 1 / p) ≤ y' s ^ (1 - 1 / p) := Real.rpow_le_rpow (hy0 s) h2 he
      have h4 := h1 p hp
      have h5 : 0 ≤ c * p * B ^ (2 / p) := mul_nonneg (mul_nonneg hc hp0.le) (Real.rpow_nonneg hB _)
      calc 2 * |Λ s| ≤ 2 * (c * p * B ^ (2 / p) * y s ^ (1 - 1 / p)) := by linarith
        _ ≤ 2 * (c * p * B ^ (2 / p) * y' s ^ (1 - 1 / p)) := by
            have := mul_le_mul_of_nonneg_left h3 h5
            linarith
        _ = _ := by ring
    have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hint1 : IntervalIntegrable (fun s => 2 * |Λ s|) volume 0 t :=
      (hii.mono_set (hsub t ht)).const_mul 2
    have hint2 : IntervalIntegrable (fun τ => (2 * c) * p * B ^ (2 / p) * y' τ ^ (1 - 1 / p)) volume 0 t := by
      refine ContinuousOn.intervalIntegrable ?_
      have hs : uIcc 0 t ⊆ Icc 0 T := by
        rw [uIcc_of_le ht.1]; exact hsubT
      refine continuousOn_const.mul (((hy'c.mono hs)).rpow_const fun x _ => Or.inr he)
    calc y' t ≤ Z t := min_le_left _ _
      _ = ∫ s in (0 : ℝ)..t, 2 * |Λ s| := by
          simp only [hZ]; rw [intervalIntegral.integral_const_mul]
      _ ≤ _ := by
          refine intervalIntegral.integral_mono_ae_restrict ht.1 hint1 hint2 ?_
          exact ae_restrict_of_ae_restrict_of_subset hsubT hae
  have hz := osgood_yudovich_global (y := y') (T := T) (K := 2 * c) (B := B) (by linarith) hB hy'c hy'0
    (fun t _ => min_le_right _ _) hmain
  filter_upwards [hyy, hmem] with t h1 ht
  exact le_antisymm (h1.trans (hz t ht).le) (hy0 t)

end PDE
