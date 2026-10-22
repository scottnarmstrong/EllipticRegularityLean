module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The heat kernel on `Vec d`

The Gaussian density `Φ(t,x) = (4πt)^{-d/2} exp(-|x|²/(4t))` on `Vec d`, its integrability and
normalization, using the coordinatewise Euclidean quadratic form `vecNormSq`.
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

/-- The heat kernel `Φ(t,x) = (4πt)^{-d/2} exp(-|x|²/(4t))`. -/
noncomputable def heat (d : ℕ) (t : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t))

theorem exp_neg_mul_vecNormSq_eq_prod {d : ℕ} (b : ℝ) (x : Vec d) :
    Real.exp (-b * vecNormSq x) = ∏ i, Real.exp (-b * x i ^ 2) := by
  rw [vecNormSq_eq_sum_sq, Finset.mul_sum, Real.exp_sum]

theorem integrable_exp_neg_mul_vecNormSq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Vec d => Real.exp (-b * vecNormSq x)) := by
  simp_rw [exp_neg_mul_vecNormSq_eq_prod]
  exact Integrable.fintype_prod (f := fun _ (y : ℝ) => Real.exp (-b * y ^ 2))
    fun _ => integrable_exp_neg_mul_sq hb

theorem integral_exp_neg_mul_vecNormSq {d : ℕ} (b : ℝ) :
    ∫ x : Vec d, Real.exp (-b * vecNormSq x) = Real.sqrt (Real.pi / b) ^ d := by
  simp_rw [exp_neg_mul_vecNormSq_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun _ (y : ℝ) => Real.exp (-b * y ^ 2))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, neg_mul]
  simp only [← neg_mul, integral_gaussian]

theorem heat_eq_mul_exp {d : ℕ} (t : ℝ) (x : Vec d) :
    heat d t x = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * vecNormSq x) := by
  unfold heat
  congr 2
  ring

theorem heat_nonneg {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Vec d) : 0 ≤ heat d t x := by
  unfold heat
  have : 0 < 4 * Real.pi * t := by positivity
  positivity

theorem continuous_heat {d : ℕ} (t : ℝ) : Continuous (heat d t) := by
  unfold heat
  have : Continuous (fun x : Vec d => vecNormSq x) := by
    have h : (fun x : Vec d => vecNormSq x) = fun x => ∑ i, x i ^ 2 :=
      funext vecNormSq_eq_sum_sq
    rw [h]
    fun_prop
  fun_prop

theorem integrable_heat {d : ℕ} {t : ℝ} (ht : 0 < t) : Integrable (heat d t : Vec d → ℝ) := by
  rw [show (heat d t : Vec d → ℝ) = _ from funext (heat_eq_mul_exp t)]
  exact (integrable_exp_neg_mul_vecNormSq (by positivity)).const_mul _

theorem integral_heat {d : ℕ} {t : ℝ} (ht : 0 < t) : ∫ x : Vec d, heat d t x = 1 := by
  simp_rw [heat_eq_mul_exp]
  rw [integral_const_mul, integral_exp_neg_mul_vecNormSq]
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by field_simp
  rw [this, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h4.le,
    ← Real.rpow_add h4]
  have : (-(d : ℝ) / 2 + 1 / 2 * (d : ℝ)) = 0 := by ring
  rw [this, Real.rpow_zero]

end PDE.GaussianPoincare
