module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Mollify

/-!
# Friedland--Hayman: Barta's inequality for Lipschitz test functions

If `g` is Lipschitz and vanishes on `(-∞, τ]`, then the box averages `box g (1 / (k + 1))` are
admissible `GaussTest` functions; their energies and masses converge (dominated convergence,
using Rademacher's theorem for the derivative), so Barta's inequality passes to the limit.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

namespace LipBarta

noncomputable section

theorem integrable_sq_mul {τ : ℝ} {K : NNReal} {f : ℝ → ℝ} (hc : Continuous f)
    (hb : ∀ s, |f s| ≤ K * max (s - τ) 0) : Integrable fun s => f s ^ 2 * gaussW s := by
  have hI : Integrable fun s : ℝ =>
      (2 * (K : ℝ) ^ 2) * (s ^ 2 * gaussW s) + (2 * (K : ℝ) ^ 2 * τ ^ 2) * gaussW s :=
    (integrable_sq_mul_gaussW.const_mul _).add (integrable_gaussW.const_mul _)
  refine Integrable.mono' hI ((hc.pow 2).mul continuous_gaussW).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  have h1 : f s ^ 2 ≤ ((K : ℝ) * max (s - τ) 0) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (hb s) 2
    rwa [sq_abs] at this
  have hm : max (s - τ) 0 ^ 2 ≤ 2 * s ^ 2 + 2 * τ ^ 2 := by
    rcases le_total (s - τ) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg s, sq_nonneg τ]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg (s + τ)]
  have h2 : ((K : ℝ) * max (s - τ) 0) ^ 2 ≤ 2 * (K : ℝ) ^ 2 * s ^ 2 + 2 * (K : ℝ) ^ 2 * τ ^ 2 := by
    calc ((K : ℝ) * max (s - τ) 0) ^ 2 = (K : ℝ) ^ 2 * max (s - τ) 0 ^ 2 := mul_pow _ _ _
      _ ≤ (K : ℝ) ^ 2 * (2 * s ^ 2 + 2 * τ ^ 2) :=
          mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = _ := by ring
  have hw := gaussW_pos s
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc f s ^ 2 * gaussW s ≤ (2 * (K : ℝ) ^ 2 * s ^ 2 + 2 * (K : ℝ) ^ 2 * τ ^ 2) * gaussW s :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hw.le
    _ = _ := by ring

theorem gaussTest_box {τ : ℝ} {K : NNReal} {g : ℝ → ℝ} (hg : LipschitzWith K g)
    (hz : ∀ s, s ≤ τ → g s = 0) {η : ℝ} (hη : 0 < η) : GaussTest τ (box g η) (dbox g η) where
  cont := continuous_box hg.continuous η
  eq_zero := fun _ hs => box_eq_zero hη hz hs
  hasDeriv := fun s _ => hasDerivAt_box hg.continuous η s
  cont' := (continuous_dbox hg.continuous η).continuousOn
  int_sq := integrable_sq_mul (continuous_box hg.continuous η) (abs_box_le hg hz hη)
  int_dsq := by
    refine Integrable.mono' ((integrable_gaussW.const_mul ((K : ℝ) ^ 2)).integrableOn)
      (((continuous_dbox hg.continuous η).pow 2).mul continuous_gaussW).aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    have hw := gaussW_pos s
    have h1 : dbox g η s ^ 2 ≤ (K : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_dbox_le hg hη s) 2
      rwa [sq_abs] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right h1 hw.le

theorem tendsto_box_sq {τ : ℝ} {K : NNReal} {g : ℝ → ℝ} (hg : LipschitzWith K g)
    (hz : ∀ s, s ≤ τ → g s = 0) {η : ℕ → ℝ} (hpos : ∀ k, 0 < η k) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun k => ∫ s, box g (η k) s ^ 2 * gaussW s) atTop
      (𝓝 (∫ s, g s ^ 2 * gaussW s)) := by
  have hbd : Integrable fun s : ℝ => ((K : ℝ) * max (s - τ) 0) ^ 2 * gaussW s :=
    integrable_sq_mul (K := K) (τ := τ) (by fun_prop) fun s => by
      rw [abs_of_nonneg (by positivity)]
  refine tendsto_integral_of_dominated_convergence _
    (fun k => ((continuous_box hg.continuous (η k)).pow 2 |>.mul
      continuous_gaussW).aestronglyMeasurable) hbd (fun k => ae_of_all _ fun s => ?_)
    (ae_of_all _ fun s => ?_)
  · have hw := gaussW_pos s
    have h1 : box g (η k) s ^ 2 ≤ ((K : ℝ) * max (s - τ) 0) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_box_le hg hz (hpos k) s) 2
      rwa [sq_abs] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right h1 hw.le
  · have h : Tendsto (fun k => box g (η k) s) atTop (𝓝 (g s)) := by
      have h0 : Tendsto (fun k => (K : ℝ) * η k) atTop (𝓝 0) := by
        simpa using hη.const_mul (K : ℝ)
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h0
      rw [Real.norm_eq_abs]
      exact abs_box_sub_le hg (hpos k) s
    exact ((h.pow 2).mul_const _)

theorem tendsto_dbox_sq {τ : ℝ} {K : NNReal} {g : ℝ → ℝ} (hg : LipschitzWith K g)
    {η : ℕ → ℝ} (hpos : ∀ k, 0 < η k) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun k => ∫ s in Ioi τ, dbox g (η k) s ^ 2 * gaussW s) atTop
      (𝓝 (∫ s in Ioi τ, deriv g s ^ 2 * gaussW s)) := by
  refine tendsto_integral_of_dominated_convergence _
    (fun k => ((continuous_dbox hg.continuous (η k)).pow 2 |>.mul
      continuous_gaussW).aestronglyMeasurable)
    (integrable_gaussW.const_mul ((K : ℝ) ^ 2)).integrableOn
    (fun k => ae_of_all _ fun s => ?_) ?_
  · have hw := gaussW_pos s
    have h1 : dbox g (η k) s ^ 2 ≤ (K : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_dbox_le hg (hpos k) s) 2
      rwa [sq_abs] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right h1 hw.le
  · refine ae_restrict_of_ae ?_
    filter_upwards [hg.ae_differentiableAt_real] with s hs
    have hd := hs.hasDerivAt
    have h0 := hasDerivAt_iff_tendsto_slope_zero.1 hd
    have hneg : Tendsto (fun k => -η k) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa using hη.neg,
        Eventually.of_forall fun k => by simpa using (hpos k).ne'⟩
    have h1 := h0.comp hneg
    have h2 : Tendsto (fun k => dbox g (η k) s) atTop (𝓝 (deriv g s)) := by
      refine h1.congr fun k => ?_
      simp only [Function.comp_apply, dbox, smul_eq_mul]
      rw [show s + -η k = s - η k by ring, inv_neg]
      ring
    exact ((h2.pow 2).mul_const _)

end

end LipBarta

open LipBarta in
/-- Barta's inequality for Lipschitz test functions vanishing on `(-∞, τ]`. -/
theorem gaussBeta_barta_lipschitz {τ : ℝ} {K : NNReal} {g : ℝ → ℝ} (hg : LipschitzWith K g)
    (hz : ∀ s, s ≤ τ → g s = 0) :
    gaussBeta τ * ∫ s, g s ^ 2 * gaussW s ≤ ∫ s in Set.Ioi τ, deriv g s ^ 2 * gaussW s := by
  have hpos : ∀ k : ℕ, 0 < (1 : ℝ) / ((k : ℝ) + 1) := fun k => by positivity
  have hη : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto_of_tendsto' ((tendsto_box_sq hg hz hpos hη).const_mul _)
    (tendsto_dbox_sq hg hpos hη) fun k => gaussBeta_barta (gaussTest_box hg hz (hpos k))

end PDE.FHLane
