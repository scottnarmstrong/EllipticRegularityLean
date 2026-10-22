module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Fourier coefficients on `[0, 2π]` in terms of cosine and sine integrals

For a real function `g` interval integrable on `[0, 2π]`, the Fourier coefficient
`fourierCoeffOn` of `g` is `(A - i B) / (2π)` with `A = ∫ cos(n θ) g` and
`B = ∫ sin(n θ) g`.  Integration by parts for absolutely continuous periodic
functions then relates the coefficients of `w'` to those of `w`.
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory

/-- The interval `[0, 2π]` as `a < b`. -/
theorem zero_lt_two_pi' : (0 : ℝ) < 2 * Real.pi := by positivity

/-- Fourier coefficient of a real function via cosine and sine integrals. -/
theorem fourierCoeffOn_ofReal {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn zero_lt_two_pi' (fun x => (g x : ℂ)) n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (((∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * g x : ℝ) : ℂ) -
          Complex.I * ((∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin (n * x) * g x : ℝ) : ℂ)) := by
  rw [fourierCoeffOn_eq_integral _ _ zero_lt_two_pi']
  have hc : IntervalIntegrable (fun x => Real.cos (n * x) * g x) volume 0 (2 * Real.pi) :=
    hg.continuousOn_mul (by fun_prop)
  have hs : IntervalIntegrable (fun x => Real.sin (n * x) * g x) volume 0 (2 * Real.pi) :=
    hg.continuousOn_mul (by fun_prop)
  have hpt : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * Real.pi - 0)) • (g x : ℂ) =
      ((Real.cos (n * x) * g x : ℝ) : ℂ) - Complex.I * ((Real.sin (n * x) * g x : ℝ) : ℂ) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul]
    have : (2 * Real.pi - 0 : ℝ) ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
    have h2 : (2 * ↑Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / ((2 * Real.pi - 0 : ℝ) : ℂ)) =
        -((n * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp
      ring
    rw [h2, Complex.exp_mul_I]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [hpt]
  have hcC : IntervalIntegrable (fun x => ((Real.cos (n * x) * g x : ℝ) : ℂ)) volume 0
      (2 * Real.pi) := ⟨hc.1.ofReal, hc.2.ofReal⟩
  have hsC : IntervalIntegrable (fun x => ((Real.sin (n * x) * g x : ℝ) : ℂ)) volume 0
      (2 * Real.pi) := ⟨hs.1.ofReal, hs.2.ofReal⟩
  rw [intervalIntegral.integral_sub hcC (hsC.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  simp only [sub_zero, Complex.real_smul]

/-- Squared norm of the Fourier coefficient of a real function. -/
theorem norm_sq_fourierCoeffOn_ofReal {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (n : ℤ) :
    ‖fourierCoeffOn zero_lt_two_pi' (fun x => (g x : ℂ)) n‖ ^ 2 =
      (1 / (2 * Real.pi)) ^ 2 *
        ((∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * g x) ^ 2 +
          (∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin (n * x) * g x) ^ 2) := by
  rw [fourierCoeffOn_ofReal hg n, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- Integration by parts against `cos (n θ)`. -/
theorem integral_cos_mul_deriv {w : ℝ → ℝ}
    (hper : Function.Periodic w (2 * Real.pi))
    (hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi)) (n : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * deriv w x =
      n * ∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin (n * x) * w x := by
  have hcos : AbsolutelyContinuousOnInterval (fun x : ℝ => Real.cos (n * x)) 0 (2 * Real.pi) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (show ContDiff ℝ 1 (fun x : ℝ => Real.cos (n * x)) from Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have := hcos.integral_mul_deriv_eq_deriv_mul hac
  rw [this]
  have hd : deriv (fun x : ℝ => Real.cos (n * x)) = fun x => -(n * Real.sin (n * x)) := by
    funext x
    have h : HasDerivAt (fun x : ℝ => Real.cos (n * x)) (-Real.sin (n * x) * n) x := by
      have h0 : HasDerivAt (fun x : ℝ => (n : ℝ) * x) n x := by
        simpa using (hasDerivAt_id x).const_mul (n : ℝ)
      exact h0.cos
    rw [h.deriv]; ring
  rw [hd]
  have h0 : w (2 * Real.pi) = w 0 := by simpa using hper 0
  have hc : Real.cos (n * (2 * Real.pi)) = 1 := by
    rw [show (n : ℝ) * (2 * Real.pi) = n * (2 * Real.pi) from rfl]
    exact Real.cos_int_mul_two_pi n
  simp only [hc, h0, mul_zero, Real.cos_zero]
  rw [← intervalIntegral.integral_const_mul]
  simp only [neg_mul, intervalIntegral.integral_neg]
  have : ∀ x : ℝ, (n : ℝ) * Real.sin (n * x) * w x = n * (Real.sin (n * x) * w x) := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Integration by parts against `sin (n θ)`. -/
theorem integral_sin_mul_deriv {w : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi)) (n : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin (n * x) * deriv w x =
      -(n * ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * w x) := by
  have hsin : AbsolutelyContinuousOnInterval (fun x : ℝ => Real.sin (n * x)) 0 (2 * Real.pi) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (show ContDiff ℝ 1 (fun x : ℝ => Real.sin (n * x)) from Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have := hsin.integral_mul_deriv_eq_deriv_mul hac
  rw [this]
  have hd : deriv (fun x : ℝ => Real.sin (n * x)) = fun x => n * Real.cos (n * x) := by
    funext x
    have h : HasDerivAt (fun x : ℝ => Real.sin (n * x)) (Real.cos (n * x) * n) x := by
      have h0 : HasDerivAt (fun x : ℝ => (n : ℝ) * x) n x := by
        simpa using (hasDerivAt_id x).const_mul (n : ℝ)
      exact h0.sin
    rw [h.deriv]; ring
  rw [hd]
  have hs : Real.sin (n * (2 * Real.pi)) = 0 := by simpa using Real.sin_periodic.int_mul n 0
  simp only [hs, mul_zero, Real.sin_zero, zero_mul, sub_zero]
  have : ∀ x : ℝ, (n : ℝ) * Real.cos (n * x) * w x = n * (Real.cos (n * x) * w x) := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The Fourier coefficients of `w'` are `n²` times those of `w`, in norm. -/
theorem norm_sq_fourierCoeffOn_deriv {w : ℝ → ℝ}
    (hper : Function.Periodic w (2 * Real.pi))
    (hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi)) (n : ℤ) :
    ‖fourierCoeffOn zero_lt_two_pi' (fun x => ((deriv w x : ℝ) : ℂ)) n‖ ^ 2 =
      (n : ℝ) ^ 2 * ‖fourierCoeffOn zero_lt_two_pi' (fun x => (w x : ℂ)) n‖ ^ 2 := by
  rw [norm_sq_fourierCoeffOn_ofReal hac.intervalIntegrable_deriv,
    norm_sq_fourierCoeffOn_ofReal (hac.continuousOn.intervalIntegrable),
    integral_cos_mul_deriv hper hac, integral_sin_mul_deriv hac]
  ring

end PDE.Ch4Planar
