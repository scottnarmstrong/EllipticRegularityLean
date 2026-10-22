module

public import PDEFoundation.Analysis.ComplexWeightedEndpoints
public import PDEFoundation.Analysis.FiniteExponentialStrip
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators

namespace PDE

noncomputable section

variable {ι κ : Type*}

local instance : DecidableEq ι := Classical.decEq ι

/-- The coordinatewise complexification of a real linear map is given by its
matrix coefficients on the canonical finite basis. -/
theorem coordinatewiseComplexification_eq_sum [Fintype ι]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℂ) (j : κ) :
    coordinatewiseComplexification T f j =
      ∑ i, (T (Pi.single i 1) j : ℂ) * f i := by
  have hreal (g : ι → ℝ) : T g j = ∑ i, T (Pi.single i 1) j * g i := by
    have hg : g = ∑ i, (g i) • (Pi.single i 1 : ι → ℝ) := pi_eq_sum_univ' g
    calc
      T g j = T (∑ i, (g i) • (Pi.single i 1 : ι → ℝ)) j := by rw [← hg]
      _ = ∑ i, T (Pi.single i 1) j * g i := by
        rw [map_sum]
        rw [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
        ring
  apply Complex.ext
  · simp only [coordinatewiseComplexification_re, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact hreal (fun i => (f i).re)
  · simp only [coordinatewiseComplexification_im, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact hreal (fun i => (f i).im)

/-- Pairing exponential input and test families through a complexified real
linear map produces one finite exponential sum on the product index. -/
theorem exponentialPairing_eq_finiteExponentialSum
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (v : κ → ℝ) (c : ι → ℂ) (a : ι → ℝ) (b : ι → ℂ)
    (e : κ → ℂ) (k : κ → ℝ) (h : κ → ℂ) (z : ℂ) :
    (∑ j, (v j : ℂ) *
      coordinatewiseComplexification T
        (fun i => c i * Complex.exp ((a i : ℂ) * z + b i)) j *
      (e j * Complex.exp ((k j : ℂ) * z + h j))) =
      finiteExponentialSum
        (fun r : ι × κ =>
          (v r.2 : ℂ) * (T (Pi.single r.1 1) r.2 : ℂ) * c r.1 * e r.2)
        (fun r : ι × κ => b r.1 + h r.2)
        (fun r : ι × κ => a r.1 + k r.2) z := by
  simp_rw [coordinatewiseComplexification_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [finiteExponentialSum, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hexp :
      Complex.exp ((a j : ℂ) * z + b j) * Complex.exp ((k i : ℂ) * z + h i) =
        Complex.exp (((a j + k i : ℝ) : ℂ) * z + (b j + h i)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hexp]
  ring

end

end PDE
