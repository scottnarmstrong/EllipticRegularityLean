module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun


/-!
# Absolutely continuous chain rule in time

For `v(τ) = v(s) + ∫_s^τ D` (an absolutely continuous function) and a `C¹` function `ψ`,
`½ ψ² v²` is absolutely continuous with derivative `ψ ψ' v² + ψ² v D` almost everywhere.
-/

@[expose] public section

namespace PDE.Parabolic.Energy

open MeasureTheory Set intervalIntegral

theorem time_energy_identity {s t : ℝ} (hst : s ≤ t) {v D ψ : ℝ → ℝ}
    (hD : IntervalIntegrable D volume s t)
    (hv : ∀ τ ∈ Icc s t, v τ = v s + ∫ σ in s..τ, D σ) (hψ : ContDiff ℝ 1 ψ) :
    (1 / 2 : ℝ) * ψ t ^ 2 * v t ^ 2 - (1 / 2 : ℝ) * ψ s ^ 2 * v s ^ 2 =
      ∫ τ in s..t, (ψ τ * deriv ψ τ * v τ ^ 2 + ψ τ ^ 2 * v τ * D τ) := by
  set w : ℝ → ℝ := fun τ => v s + ∫ σ in s..τ, D σ with hw
  have hws : s ∈ uIcc s t := left_mem_uIcc
  have hwac : AbsolutelyContinuousOnInterval w s t :=
    ((contDiffOn_const (c := v s)).absolutelyContinuousOnInterval (a := s) (b := t)).add
      (hD.absolutelyContinuousOnInterval_intervalIntegral hws)
  have hψac : AbsolutelyContinuousOnInterval ψ s t :=
    (hψ.contDiffOn (s := uIcc s t)).absolutelyContinuousOnInterval
  have hFac : AbsolutelyContinuousOnInterval
      (fun τ => (1 / 2 : ℝ) * (ψ τ * ψ τ * (w τ * w τ))) s t :=
    ((hψac.fun_mul hψac).fun_mul (hwac.fun_mul hwac)).const_mul _
  have hFTC := hFac.integral_deriv_eq_sub
  have hwv : ∀ τ ∈ Icc s t, w τ = v τ := fun τ hτ => (hv τ hτ).symm
  have hae : ∀ᵐ τ, τ ∈ uIcc s t → HasDerivAt w (D τ) τ := by
    filter_upwards [hD.ae_hasDerivAt_integral] with τ hτ hτm
    exact (hτ hτm s hws).const_add (v s)
  have hae2 : ∀ᵐ τ, τ ∈ uIoc s t →
      deriv (fun τ => (1 / 2 : ℝ) * (ψ τ * ψ τ * (w τ * w τ))) τ =
        ψ τ * deriv ψ τ * w τ ^ 2 + ψ τ ^ 2 * w τ * D τ := by
    filter_upwards [hae] with τ hτ hτm
    have hd := hτ (uIoc_subset_uIcc hτm)
    have hψd : HasDerivAt ψ (deriv ψ τ) τ :=
      ((hψ.differentiable (by norm_num)) τ).hasDerivAt
    have h := ((hψd.mul hψd).mul (hd.mul hd)).const_mul (1 / 2 : ℝ)
    have h' : HasDerivAt (fun τ => (1 / 2 : ℝ) * (ψ τ * ψ τ * (w τ * w τ)))
        ((1 / 2 : ℝ) * ((deriv ψ τ * ψ τ + ψ τ * deriv ψ τ) * (w τ * w τ) +
          (ψ τ * ψ τ) * (D τ * w τ + w τ * D τ))) τ := h
    rw [h'.deriv]
    ring
  have hint : ∫ τ in s..t, deriv (fun τ => (1 / 2 : ℝ) * (ψ τ * ψ τ * (w τ * w τ))) τ =
      ∫ τ in s..t, (ψ τ * deriv ψ τ * v τ ^ 2 + ψ τ ^ 2 * v τ * D τ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae2] with τ hτ hτm
    rw [hτ hτm]
    have hτI : τ ∈ Icc s t := by
      rcases uIoc_of_le hst ▸ hτm with ⟨h1, h2⟩
      exact ⟨h1.le, h2⟩
    rw [hwv τ hτI]
  rw [← hint, hFTC]
  have hts : w s = v s := by simp [hw]
  have htt : w t = v t := hwv t ⟨hst, le_rfl⟩
  simp only [hts, htt]
  ring

end PDE.Parabolic.Energy
