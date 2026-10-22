module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Beta
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Friedland--Hayman: one-sided box averages of a Lipschitz function

For a continuous `g` vanishing on `(-∞, τ]` and `η > 0`, the one-sided box average
`box g η s = η⁻¹ ∫_{s-η}^{s} g` is `C¹`, vanishes on `(-∞, τ]`, has derivative
`η⁻¹ (g s - g (s - η))`, and (for Lipschitz `g`) converges to `g` as `η → 0`.  These are the
admissible test functions in the approximation of Barta's inequality for Lipschitz functions.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

namespace LipBarta

noncomputable section

/-- One-sided box average of `g` over `[s - η, s]`. -/
def box (g : ℝ → ℝ) (η s : ℝ) : ℝ := η⁻¹ * ∫ v in (s - η)..s, g v

/-- Derivative of the box average. -/
def dbox (g : ℝ → ℝ) (η s : ℝ) : ℝ := η⁻¹ * (g s - g (s - η))

theorem hasDerivAt_box {g : ℝ → ℝ} (hg : Continuous g) (η s : ℝ) :
    HasDerivAt (box g η) (dbox g η s) s := by
  have hF : ∀ u, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g u) u := fun u =>
    (hg.integral_hasStrictDerivAt 0 u).hasDerivAt
  have h1 := (hF s).sub ((hF (s - η)).comp_sub_const s η)
  have h2 := h1.const_mul η⁻¹
  have e : box g η = fun x => η⁻¹ * ((∫ t in (0 : ℝ)..x, g t) - ∫ t in (0 : ℝ)..(x - η), g t) := by
    funext x
    unfold box
    rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)]
  rw [e]
  exact h2

theorem continuous_box {g : ℝ → ℝ} (hg : Continuous g) (η : ℝ) : Continuous (box g η) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_box hg η s).continuousAt

theorem continuous_dbox {g : ℝ → ℝ} (hg : Continuous g) (η : ℝ) : Continuous (dbox g η) := by
  unfold dbox
  fun_prop

theorem box_eq_zero {g : ℝ → ℝ} {τ η s : ℝ} (hη : 0 < η) (hz : ∀ s, s ≤ τ → g s = 0)
    (hs : s ≤ τ) : box g η s = 0 := by
  unfold box
  have : ∫ v in (s - η)..s, g v = ∫ v in (s - η)..s, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by linarith)] at hv
    exact hz v (hv.2.trans hs)
  rw [this]
  simp

theorem abs_le_max {g : ℝ → ℝ} {K : NNReal} {τ : ℝ} (hg : LipschitzWith K g)
    (hz : ∀ s, s ≤ τ → g s = 0) (s : ℝ) : |g s| ≤ K * max (s - τ) 0 := by
  by_cases h : s ≤ τ
  · rw [hz s h]
    simp [max_eq_right (sub_nonpos.2 h)]
  · push Not at h
    have := hg.dist_le_mul s τ
    rw [Real.dist_eq, Real.dist_eq, hz τ le_rfl, sub_zero, abs_of_pos (sub_pos.2 h)] at this
    rw [max_eq_left (sub_pos.2 h).le]
    exact this

theorem abs_box_le {g : ℝ → ℝ} {K : NNReal} {τ η : ℝ} (hg : LipschitzWith K g)
    (hz : ∀ s, s ≤ τ → g s = 0) (hη : 0 < η) (s : ℝ) :
    |box g η s| ≤ K * max (s - τ) 0 := by
  unfold box
  have hb : ‖∫ v in (s - η)..s, g v‖ ≤ (K * max (s - τ) 0) * |s - (s - η)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_
    rw [Set.uIoc_of_le (by linarith)] at hv
    rw [Real.norm_eq_abs]
    refine (abs_le_max hg hz v).trans ?_
    gcongr
    exact hv.2
  rw [abs_mul, abs_of_pos (inv_pos.2 hη)]
  rw [Real.norm_eq_abs, show s - (s - η) = η by ring, abs_of_pos hη] at hb
  calc η⁻¹ * |∫ v in (s - η)..s, g v| ≤ η⁻¹ * ((K * max (s - τ) 0) * η) := by gcongr
    _ = K * max (s - τ) 0 := by field_simp

theorem abs_dbox_le {g : ℝ → ℝ} {K : NNReal} (hg : LipschitzWith K g) {η : ℝ} (hη : 0 < η)
    (s : ℝ) : |dbox g η s| ≤ K := by
  unfold dbox
  have := hg.dist_le_mul s (s - η)
  rw [Real.dist_eq, Real.dist_eq, show s - (s - η) = η by ring, abs_of_pos hη] at this
  rw [abs_mul, abs_of_pos (inv_pos.2 hη)]
  calc η⁻¹ * |g s - g (s - η)| ≤ η⁻¹ * (K * η) := by gcongr
    _ = K := by field_simp

theorem abs_box_sub_le {g : ℝ → ℝ} {K : NNReal} (hg : LipschitzWith K g) {η : ℝ} (hη : 0 < η)
    (s : ℝ) : |box g η s - g s| ≤ K * η := by
  have hi : IntervalIntegrable g volume (s - η) s := hg.continuous.intervalIntegrable _ _
  have e : box g η s - g s = η⁻¹ * ∫ v in (s - η)..s, (g v - g s) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel]
    unfold box
    field_simp
  have hb : ‖∫ v in (s - η)..s, (g v - g s)‖ ≤ (K * η) * |s - (s - η)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_
    rw [Set.uIoc_of_le (by linarith)] at hv
    rw [Real.norm_eq_abs]
    have := hg.dist_le_mul v s
    rw [Real.dist_eq, Real.dist_eq] at this
    refine this.trans ?_
    have h2 : |v - s| ≤ η := by
      rw [abs_of_nonpos (by linarith [hv.2])]
      linarith [hv.1]
    gcongr
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hη)]
  rw [Real.norm_eq_abs, show s - (s - η) = η by ring, abs_of_pos hη] at hb
  calc η⁻¹ * |∫ v in (s - η)..s, (g v - g s)| ≤ η⁻¹ * ((K * η) * η) := by gcongr
    _ = K * η := by field_simp

end

end LipBarta

end PDE.FHLane
