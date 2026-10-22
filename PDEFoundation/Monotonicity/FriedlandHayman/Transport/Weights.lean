module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Friedland--Hayman: cap fractions and Gaussian tails

`sinW D φ = sin φ ^ (D - 2)` is the zonal weight on `[0, π]`; `capFrac D θ` is the normalized
measure of the polar cap of angular radius `θ`; `gaussTail t` is the standard Gaussian tail.
We prove the monotonicity, continuity, derivative and limit facts used by the transport map.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- Zonal weight `sin^{D-2}` on `[0, π]`. -/
noncomputable def sinW (D : ℕ) (φ : ℝ) : ℝ := Real.sin φ ^ (D - 2)

/-- Normalized measure of the polar cap of angular radius `θ` in `S^{D-1}`. -/
noncomputable def capFrac (D : ℕ) (θ : ℝ) : ℝ :=
  (∫ φ in (0 : ℝ)..θ, sinW D φ) / ∫ φ in (0 : ℝ)..Real.pi, sinW D φ

/-- Gaussian tail `γ((t, ∞))`. -/
noncomputable def gaussTail (t : ℝ) : ℝ := (∫ s in Set.Ioi t, gaussW s) / ∫ s, gaussW s

namespace Transp

/-- Total zonal mass. -/
def zTot (D : ℕ) : ℝ := ∫ φ in (0 : ℝ)..Real.pi, sinW D φ

/-- Total Gaussian mass. -/
def gTot : ℝ := ∫ s, gaussW s

end Transp

open Transp

theorem continuous_sinW (D : ℕ) : Continuous (sinW D) :=
  Real.continuous_sin.pow _

theorem sinW_pos {D : ℕ} {φ : ℝ} (h : φ ∈ Set.Ioo 0 Real.pi) : 0 < sinW D φ :=
  pow_pos (Real.sin_pos_of_pos_of_lt_pi h.1 h.2) _

theorem Transp.zTot_pos (D : ℕ) : 0 < zTot D :=
  intervalIntegral.intervalIntegral_pos_of_pos_on ((continuous_sinW D).intervalIntegrable _ _)
    (fun _ hx => sinW_pos hx) Real.pi_pos

theorem Transp.gTot_pos : 0 < gTot := by
  unfold gTot
  rw [integral_pos_iff_support_of_nonneg (fun s => (gaussW_pos s).le) integrable_gaussW]
  have : Function.support gaussW = Set.univ := by
    ext s
    simpa using (gaussW_pos s).ne'
  rw [this]
  simp

theorem capFrac_eq (D : ℕ) (θ : ℝ) : capFrac D θ = (∫ φ in (0 : ℝ)..θ, sinW D φ) / zTot D := rfl

theorem hasDerivAt_capFrac (D : ℕ) (θ : ℝ) :
    HasDerivAt (capFrac D) (sinW D θ / zTot D) θ :=
  (((continuous_sinW D).integral_hasStrictDerivAt 0 θ).hasDerivAt).div_const _

theorem continuous_capFrac (D : ℕ) : Continuous (capFrac D) :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_capFrac D θ).continuousAt

@[simp] theorem capFrac_zero (D : ℕ) : capFrac D 0 = 0 := by
  simp [capFrac_eq]

theorem capFrac_pi (D : ℕ) : capFrac D Real.pi = 1 := by
  rw [capFrac_eq]
  exact div_self (zTot_pos D).ne'

theorem strictMonoOn_capFrac (D : ℕ) : StrictMonoOn (capFrac D) (Set.Icc 0 Real.pi) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_capFrac D).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_capFrac D x).deriv]
  exact div_pos (sinW_pos hx) (zTot_pos D)

theorem hasDerivAt_gaussTail (t : ℝ) : HasDerivAt gaussTail (-(gaussW t) / gTot) t := by
  have hI : IntegrableOn gaussW (Set.Ioi 0) := integrable_gaussW.integrableOn
  have e : (fun t => ∫ s in Set.Ioi t, gaussW s) =
      fun t => (∫ s in Set.Ioi (0 : ℝ), gaussW s) - ∫ s in (0 : ℝ)..t, gaussW s := by
    funext t
    have := intervalIntegral.integral_Ioi_sub_Ioi' hI (integrable_gaussW.integrableOn (s := Set.Ioi t))
    linarith
  have h1 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, gaussW s) (gaussW t) t :=
    (continuous_gaussW.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h2 := (h1.const_sub (∫ s in Set.Ioi (0 : ℝ), gaussW s)).div_const gTot
  have e2 : gaussTail = fun t => ((∫ s in Set.Ioi (0 : ℝ), gaussW s) -
      ∫ s in (0 : ℝ)..t, gaussW s) / gTot := by
    funext t
    unfold gaussTail gTot
    rw [← congrFun e t]
  rw [e2]
  exact h2

theorem continuous_gaussTail : Continuous gaussTail :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gaussTail t).continuousAt

theorem strictAnti_gaussTail : StrictAnti gaussTail := by
  refine strictAnti_of_deriv_neg fun x => ?_
  rw [(hasDerivAt_gaussTail x).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (gaussW_pos x)) gTot_pos

theorem tendsto_gaussTail_atTop : Tendsto gaussTail atTop (𝓝 0) := by
  have hI : IntegrableOn gaussW (Set.Ioi 0) := integrable_gaussW.integrableOn
  have h1 := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id) 0 hI
    tendsto_id
  have h2 := (tendsto_const_nhds (x := ∫ s in Set.Ioi (0 : ℝ), gaussW s)).sub h1
  have h3 := h2.div_const gTot
  rw [sub_self, zero_div] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have := intervalIntegral.integral_Ioi_sub_Ioi' hI (integrable_gaussW.integrableOn (s := Set.Ioi t))
  have e : (∫ s in Set.Ioi t, gaussW s) =
      (∫ s in Set.Ioi (0 : ℝ), gaussW s) - ∫ s in (0 : ℝ)..t, gaussW s := by linarith
  unfold gaussTail
  rw [e]
  rfl

theorem tendsto_gaussTail_atBot : Tendsto gaussTail atBot (𝓝 1) := by
  have hI : IntegrableOn gaussW (Set.Iic 0) := integrable_gaussW.integrableOn
  have hJ : IntegrableOn gaussW (Set.Ioi 0) := integrable_gaussW.integrableOn
  have h1 := intervalIntegral_tendsto_integral_Iic (μ := volume) (l := atBot) (a := id) 0 hI
    tendsto_id
  have h2 := (tendsto_const_nhds (x := ∫ s in Set.Ioi (0 : ℝ), gaussW s)).add h1
  have h3 := h2.div_const gTot
  have hsum := intervalIntegral.integral_Iic_add_Ioi hI hJ
  have e : ((∫ s in Set.Ioi (0 : ℝ), gaussW s) + ∫ s in Set.Iic (0 : ℝ), gaussW s) / gTot = 1 := by
    have h0 : (∫ s in Set.Ioi (0 : ℝ), gaussW s) + ∫ s in Set.Iic (0 : ℝ), gaussW s = gTot := by
      rw [add_comm]
      exact hsum
    rw [h0]
    exact div_self gTot_pos.ne'
  rw [e] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_le_atBot 0] with t ht
  have := intervalIntegral.integral_Ioi_sub_Ioi' hJ (integrable_gaussW.integrableOn (s := Set.Ioi t))
  rw [intervalIntegral.integral_symm] at this
  have e : (∫ s in Set.Ioi t, gaussW s) =
      (∫ s in Set.Ioi (0 : ℝ), gaussW s) + ∫ s in t..0, gaussW s := by linarith
  unfold gaussTail
  rw [e]
  rfl

theorem gaussTail_pos (t : ℝ) : 0 < gaussTail t := by
  have h := strictAnti_gaussTail.antitone.le_of_tendsto tendsto_gaussTail_atTop (t + 1)
  exact lt_of_le_of_lt h (strictAnti_gaussTail (by linarith))

theorem gaussTail_lt_one (t : ℝ) : gaussTail t < 1 := by
  have h := strictAnti_gaussTail.antitone.ge_of_tendsto tendsto_gaussTail_atBot (t - 1)
  exact lt_of_lt_of_le (strictAnti_gaussTail (by linarith : t - 1 < t)) h

end

end PDE.FHLane
