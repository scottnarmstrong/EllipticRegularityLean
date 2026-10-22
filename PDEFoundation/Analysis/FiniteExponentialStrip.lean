module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open scoped BigOperators

namespace PDE

variable {ι : Type*}

/-- A finite sum of complex exponentials with real slopes. -/
noncomputable def finiteExponentialSum [Fintype ι]
    (c b : ι → ℂ) (a : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, c i * Complex.exp ((a i : ℂ) * z + b i)

/-- A finite exponential sum with real slopes is differentiable on the complex plane. -/
theorem finiteExponentialSum_differentiable [Fintype ι]
    (c b : ι → ℂ) (a : ι → ℝ) :
    Differentiable ℂ (finiteExponentialSum c b a) := by
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.const_mul
  exact Complex.differentiable_exp.comp
    ((differentiable_id.const_mul (a i : ℂ)).add (differentiable_const (b i)))

/-- A finite exponential sum with real slopes is continuous on the complex plane. -/
theorem finiteExponentialSum_continuous [Fintype ι]
    (c b : ι → ℂ) (a : ι → ℝ) :
    Continuous (finiteExponentialSum c b a) :=
  (finiteExponentialSum_differentiable c b a).continuous

/-- On the closed unit strip, a finite exponential sum is bounded by the
sum of the larger endpoint modulus bounds of its summands. -/
theorem norm_finiteExponentialSum_le [Fintype ι]
    (c b : ι → ℂ) (a : ι → ℝ) (z : ℂ)
    (hzZero : 0 ≤ z.re) (hzOne : z.re ≤ 1) :
    ‖finiteExponentialSum c b a z‖ ≤
      ∑ i, ‖c i‖ * Real.exp (max (b i).re ((b i).re + a i)) := by
  apply (norm_sum_le Finset.univ
    (fun i => c i * Complex.exp ((a i : ℂ) * z + b i))).trans
  apply Finset.sum_le_sum
  intro i _
  have haffine : (b i).re + a i * z.re ≤ max (b i).re ((b i).re + a i) := by
    by_cases hai : 0 ≤ a i
    · have hmul : a i * z.re ≤ a i := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hzOne hai
      linarith only [hmul, le_max_right (b i).re ((b i).re + a i)]
    · have hai' : a i ≤ 0 := le_of_not_ge hai
      have hmul : a i * z.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hai' hzZero
      linarith only [hmul, le_max_left (b i).re ((b i).re + a i)]
  rw [Complex.norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg (c i))
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  calc
    a i * z.re + (b i).re = (b i).re + a i * z.re := add_comm _ _
    _ ≤ max (b i).re ((b i).re + a i) := haffine

end PDE
