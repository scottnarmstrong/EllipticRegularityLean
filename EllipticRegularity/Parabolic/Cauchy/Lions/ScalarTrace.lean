module

public import EllipticRegularity.Parabolic.Cauchy.Lions.EnergyFields
public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitiveRepresentation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Scalar time traces from weak time derivatives

This is the one-dimensional endpoint step for the Lions fields.  It records explicitly how a
weak derivative on the open time interval and one terminal-zero test identity determine the
initial value of the continuous scalar representative.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace PDE.Parabolic.Lions

/-- A scalar weak time derivative together with one terminal-zero boundary identity determines
the initial value of the continuous representative. -/
theorem exists_scalar_time_representative_with_initial_value
    {s T q : ℝ} (hsT : s < T) {A B g : ℝ → ℝ}
    (hAopen : MemLp A 2 (volume.restrict (Ioo s T)))
    (hg : MemLp g 2 (volume.restrict (Icc s T)))
    (hweak : HasWeakDerivOnIoo s T A g)
    (hBg : B =ᵐ[volume.restrict (Icc s T)] fun t => -g t)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (hθT : θ T = 0) (hθs : θ s = 1)
    (htrace : ∫ t in Icc s T, (-(A t * deriv θ t) + B t * θ t) = q) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc s T) ∧
      A =ᵐ[volume.restrict (Icc s T)] v ∧ v s = q ∧
      ∀ x ∈ Icc s T, ∀ y ∈ Icc s T,
        v y - v x = ∫ t in x..y, g t := by
  obtain ⟨c, hAe⟩ :=
    ae_eq_intervalPrimitive_add_const_of_hasWeakDerivOnIoo hsT hAopen hg hweak
  let v : ℝ → ℝ := fun t => intervalPrimitive s g t + c
  have hgInt : IntegrableOn g (Icc s T) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  have hgInterval : IntervalIntegrable g volume s T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsT.le]
    exact hgInt
  have hvCont : ContinuousOn v (Icc s T) := by
    dsimp [v]
    exact (continuousOn_intervalPrimitive hsT.le hgInt).add continuousOn_const
  have hAeIcc : A =ᵐ[volume.restrict (Icc s T)] v := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hAe
  have hVabs : AbsolutelyContinuousOnInterval v s T := by
    have hp : AbsolutelyContinuousOnInterval (intervalPrimitive s g) s T := by
      exact hgInterval.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) s T := by
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn
        |> ContDiffOn.absolutelyContinuousOnInterval
    change AbsolutelyContinuousOnInterval
      ((fun t => intervalPrimitive s g t) + (fun _ : ℝ => c)) s T
    exact hp.add hc
  have hθabs : AbsolutelyContinuousOnInterval θ s T :=
    hθ.contDiffOn.absolutelyContinuousOnInterval
  have haeDeriv := hgInterval.ae_hasDerivAt_integral
  have hderiv : deriv v =ᵐ[volume.restrict (Icc s T)] g := by
    have hraw : ∀ᵐ t : ℝ, t ∈ Icc s T → deriv v t = g t := by
      filter_upwards [haeDeriv] with t ht
      intro htI
      have htU : t ∈ uIcc s T := by simpa [uIcc_of_le hsT.le] using htI
      have h := ht htU s (by simp [hsT.le])
      simpa [v, intervalPrimitive] using (h.add_const c).deriv
    exact (ae_restrict_iff' measurableSet_Icc).2 hraw
  have htraceV :
      ∫ t in Icc s T, (-(v t * deriv θ t) + (-g t) * θ t) = q := by
    calc
      ∫ t in Icc s T, (-(v t * deriv θ t) + (-g t) * θ t) =
          ∫ t in Icc s T, (-(A t * deriv θ t) + B t * θ t) := by
        apply integral_congr_ae
        filter_upwards [hAeIcc, hBg] with t hAt hBt
        rw [hAt, hBt]
      _ = q := htrace
  have htraceInterval :
      ∫ t in s..T, (-(v t * deriv θ t) + (-g t) * θ t) = q := by
    have hIcc := htraceV
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsT.le] at hIcc
    exact hIcc
  have hIBP := hθabs.integral_mul_deriv_eq_deriv_mul hVabs
  have hderivIntegral :
      ∫ t in s..T, θ t * deriv v t = ∫ t in s..T, θ t * g t := by
    have hderivRaw : ∀ᵐ t ∂volume, t ∈ Icc s T → deriv v t = g t :=
      (ae_restrict_iff' measurableSet_Icc).1 hderiv
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderivRaw] with t ht hI
    have hIoc : t ∈ Ioc s T := by simpa [uIoc_of_le hsT.le] using hI
    rw [ht ⟨hIoc.1.le, hIoc.2⟩]
  have hrewrite :
      ∫ t in s..T, (-(v t * deriv θ t) + (-g t) * θ t) = v s := by
    have hvContU : ContinuousOn v (uIcc s T) := by
      simpa [uIcc_of_le hsT.le] using hvCont
    have hInt1 : IntervalIntegrable (fun t => v t * deriv θ t) volume s T := by
      exact hvContU.intervalIntegrable.mul_continuousOn
        (hθ.continuous_deriv (by norm_num)).continuousOn
    have hInt2 : IntervalIntegrable (fun t => g t * θ t) volume s T :=
      hgInterval.mul_continuousOn hθ.continuous.continuousOn
    have hInt3 : IntervalIntegrable (fun t => deriv θ t * v t) volume s T := by
      exact (hθ.continuous_deriv (by norm_num)).continuousOn.intervalIntegrable
        |>.mul_continuousOn hvContU
    have hInt4 : IntervalIntegrable (fun t => θ t * g t) volume s T := by
      simpa only [mul_comm] using hInt2
    have hsum :
        (∫ t in s..T, deriv θ t * v t) + ∫ t in s..T, θ t * deriv v t =
          θ T * v T - θ s * v s := by
      rw [hIBP]
      ring
    calc
      ∫ t in s..T, (-(v t * deriv θ t) + (-g t) * θ t) =
          ∫ t in s..T, -((deriv θ t * v t) + (θ t * g t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = -((∫ t in s..T, deriv θ t * v t) + ∫ t in s..T, θ t * g t) := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_add hInt3 hInt4]
      _ = -(θ T * v T - θ s * v s) := by
        have hsum' := hsum
        rw [hderivIntegral] at hsum'
        linarith [hsum']
      _ = v s := by simp [hθT, hθs]
  have hq : q = v s := by
    rw [← htraceInterval, hrewrite]
  refine ⟨v, hvCont, hAeIcc, hq.symm, ?_⟩
  intro x hx y hy
  calc
    v y - v x = intervalPrimitive s g y - intervalPrimitive s g x := by
      simp [v]
    _ = ∫ t in x..y, g t := intervalPrimitive_sub_eq_intervalIntegral hgInt hx hy

end PDE.Parabolic.Lions
