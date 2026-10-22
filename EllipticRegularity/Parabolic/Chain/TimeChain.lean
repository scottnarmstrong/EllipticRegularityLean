/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Energy.TimeAC
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Nonlinear chain rule along absolutely continuous time slices -/

@[expose] public section

namespace PDE.Parabolic.Chain

open MeasureTheory Set intervalIntegral

/-- Product rule for a nonlinear function of an absolutely continuous curve,
with a smooth compactly supported time weight. -/
theorem time_chain_identity {s t : ℝ} (hst : s ≤ t) {v D ψ : ℝ → ℝ}
    (hD : IntervalIntegrable D volume s t)
    (hv : ∀ τ ∈ Icc s t, v τ = v s + ∫ σ in s..τ, D σ)
    (hψ : ContDiff ℝ 1 ψ) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFLip : ∃ C : NNReal, LipschitzWith C F) :
    F (v t) * ψ t - F (v s) * ψ s =
      ∫ τ in s..t, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) := by
  set w : ℝ → ℝ := fun τ => v s + ∫ σ in s..τ, D σ with hw
  have hws : s ∈ uIcc s t := left_mem_uIcc
  have hwac : AbsolutelyContinuousOnInterval w s t :=
    ((contDiffOn_const (c := v s)).absolutelyContinuousOnInterval (a := s) (b := t)).add
      (hD.absolutelyContinuousOnInterval_intervalIntegral hws)
  obtain ⟨C, hLip⟩ := hFLip
  have hFcomp : AbsolutelyContinuousOnInterval (F ∘ w) s t :=
    hLip.comp_absolutelyContinuousOnInterval hwac
  have hψac : AbsolutelyContinuousOnInterval ψ s t :=
    (hψ.contDiffOn (s := uIcc s t)).absolutelyContinuousOnInterval
  have hprod : AbsolutelyContinuousOnInterval (fun τ => F (w τ) * ψ τ) s t := by
    convert hFcomp.mul hψac using 1
    rfl
  have hFTC := hprod.integral_deriv_eq_sub
  have hwv : ∀ τ ∈ Icc s t, w τ = v τ := fun τ hτ => (hv τ hτ).symm
  have hae : ∀ᵐ τ, τ ∈ uIcc s t → HasDerivAt w (D τ) τ := by
    filter_upwards [hD.ae_hasDerivAt_integral] with τ hτ hτm
    exact (hτ hτm s hws).const_add (v s)
  have hae2 : ∀ᵐ τ, τ ∈ uIoc s t →
      deriv (fun τ => F (w τ) * ψ τ) τ =
        deriv F (w τ) * D τ * ψ τ + F (w τ) * deriv ψ τ := by
    filter_upwards [hae] with τ hτ hτm
    have hd := hτ (uIoc_subset_uIcc hτm)
    have hFd : HasDerivAt F (deriv F (w τ)) (w τ) :=
      ((hF.differentiable (by norm_num) (w τ)).hasDerivAt)
    have hψd : HasDerivAt ψ (deriv ψ τ) τ :=
      ((hψ.differentiable (by norm_num) τ).hasDerivAt)
    have h := (hFd.comp τ hd).mul hψd
    have h' : HasDerivAt (fun τ => F (w τ) * ψ τ)
        (deriv F (w τ) * D τ * ψ τ + F (w τ) * deriv ψ τ) τ := by
      convert h using 1
      · rfl
      · simp only [Function.comp_apply]
    exact h'.deriv
  have hint : ∫ τ in s..t, deriv (fun τ => F (w τ) * ψ τ) τ =
      ∫ τ in s..t, (F (v τ) * deriv ψ τ + deriv F (v τ) * ψ τ * D τ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae2] with τ hτ hτm
    rw [hτ hτm]
    have hτI : τ ∈ Icc s t := by
      rcases uIoc_of_le hst ▸ hτm with ⟨h1, h2⟩
      exact ⟨h1.le, h2⟩
    rw [hwv τ hτI]
    ring
  rw [← hint, hFTC]
  have hts : w s = v s := by simp [hw]
  have htt : w t = v t := hwv t ⟨hst, le_rfl⟩
  simp only [hts, htt]

end PDE.Parabolic.Chain
