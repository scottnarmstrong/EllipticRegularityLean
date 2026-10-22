/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Compactly supported time derivatives integrate to zero -/

@[expose] public section

namespace PDE.Parabolic.Chain

open MeasureTheory Set PDE

/-- The time derivative of a compactly supported `C¹` field is integrable. -/
theorem integrable_parTimeDeriv {d : ℕ} (f : Vec d × ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (parTimeDeriv f) volume := by
  have hcont : Continuous (parTimeDeriv f) := by
    unfold parTimeDeriv
    have h := hf.continuous_fderiv_apply (by norm_num)
    exact h.comp (continuous_id.prodMk continuous_const)
  have hcompact0 := hfc.fderiv_apply ℝ (0, 1)
  have hcompact : HasCompactSupport (parTimeDeriv f) := by
    change HasCompactSupport (fun z => (fderiv ℝ f z) (0, 1)) at hcompact0
    exact hcompact0
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The integral of the time derivative of a compactly supported `C¹` field
vanishes. This is the time integration-by-parts step used in the classical
renormalization calculation. -/
theorem integral_parTimeDeriv_eq_zero {d : ℕ} (f : Vec d × ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∫ z, parTimeDeriv f z = 0 := by
  have hint : Integrable (parTimeDeriv f) volume := integrable_parTimeDeriv f hf hfc
  rw [MeasureTheory.Measure.volume_eq_prod (Vec d) ℝ]
  rw [integral_prod _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  have hsecC : ContDiff ℝ 1 (fun t : ℝ => f (x, t)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hsecK : HasCompactSupport (fun t : ℝ => f (x, t)) := by
    let K : Set ℝ := Prod.snd '' tsupport f
    have hK : IsCompact K := hfc.isCompact.image continuous_snd
    refine HasCompactSupport.of_support_subset_isCompact (K := K) hK ?_
    intro t ht
    have hne : f (x, t) ≠ 0 := by simpa only [Function.mem_support] using ht
    exact ⟨(x, t), subset_tsupport f hne, rfl⟩
  have hsecInt : Integrable (fun t : ℝ => f (x, t)) volume :=
    hsecC.continuous.integrable_of_hasCompactSupport hsecK
  have hsecDerivC : Continuous (deriv fun t : ℝ => f (x, t)) :=
    hsecC.continuous_deriv (by norm_num)
  have hsecDerivK : HasCompactSupport (deriv fun t : ℝ => f (x, t)) := hsecK.deriv
  have hsecDerivInt : Integrable (deriv fun t : ℝ => f (x, t)) volume :=
    hsecDerivC.integrable_of_hasCompactSupport hsecDerivK
  have hderiv (t : ℝ) : HasDerivAt (fun τ : ℝ => f (x, τ))
      (deriv (fun τ : ℝ => f (x, τ)) t) t := by
    exact (hsecC.differentiable (by norm_num) t).hasDerivAt
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hsecDerivInt hsecInt
  have heq (t : ℝ) : parTimeDeriv f (x, t) = deriv (fun τ : ℝ => f (x, τ)) t := by
    have hpair : HasDerivAt (fun τ : ℝ => (x, τ)) (0, 1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    have hcomp := (hf.differentiable (by norm_num) (x, t)).hasFDerivAt.comp t hpair
    have : HasDerivAt (fun τ : ℝ => f (x, τ)) (parTimeDeriv f (x, t)) t := by
      simpa [Function.comp_def, parTimeDeriv] using hcomp.hasDerivAt
    exact this.deriv.symm.trans (by rfl)
  rw [show (fun t : ℝ => parTimeDeriv f (x, t)) =
      fun t => deriv (fun τ : ℝ => f (x, τ)) t from funext heq]
  exact hzero

end PDE.Parabolic.Chain
