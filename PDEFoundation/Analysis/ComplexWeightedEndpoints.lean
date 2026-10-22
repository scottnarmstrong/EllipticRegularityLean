module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace PDE

variable {ι κ : Type*}

/-- Coordinatewise complexification of a real linear map between finite function spaces. -/
def coordinatewiseComplexification
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℂ) : κ → ℂ :=
  fun j => ⟨T (fun i => (f i).re) j, T (fun i => (f i).im) j⟩

@[simp]
theorem coordinatewiseComplexification_re
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℂ) (j : κ) :
    (coordinatewiseComplexification T f j).re = T (fun i => (f i).re) j :=
  rfl

@[simp]
theorem coordinatewiseComplexification_im
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℂ) (j : κ) :
    (coordinatewiseComplexification T f j).im = T (fun i => (f i).im) j :=
  rfl

private theorem fourth_power_polarization (a b : ℝ) :
    6 * (a ^ 2 + b ^ 2) ^ 2 =
      4 * a ^ 4 + 4 * b ^ 4 + (a + b) ^ 4 + (a - b) ^ 4 := by
  ring

private theorem norm_four_eq (z : ℂ) :
    ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem weighted_norm_sq_coordinatewiseComplexification_le
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (w : ι → ℝ) (v : κ → ℝ) (K : ℝ)
    (hT : ∀ g : ι → ℝ,
      ∑ j, v j * (T g j) ^ 2 ≤ K * ∑ i, w i * (g i) ^ 2)
    (f : ι → ℂ) :
    ∑ j, v j * ‖coordinatewiseComplexification T f j‖ ^ 2 ≤
      K * ∑ i, w i * ‖f i‖ ^ 2 := by
  have hre := hT (fun i => (f i).re)
  have him := hT (fun i => (f i).im)
  simp only [Complex.sq_norm, Complex.normSq_apply,
    coordinatewiseComplexification_re, coordinatewiseComplexification_im] at ⊢
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add]
  simp only [pow_two] at hre him
  linarith only [hre, him]

theorem weighted_norm_four_coordinatewiseComplexification_le
    [Fintype ι] [Fintype κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (w : ι → ℝ) (v : κ → ℝ) (K : ℝ)
    (hT : ∀ g : ι → ℝ,
      ∑ j, v j * (T g j) ^ 4 ≤ K * ∑ i, w i * (g i) ^ 4)
    (f : ι → ℂ) :
    ∑ j, v j * ‖coordinatewiseComplexification T f j‖ ^ 4 ≤
      K * ∑ i, w i * ‖f i‖ ^ 4 := by
  let a : ι → ℝ := fun i => (f i).re
  let b : ι → ℝ := fun i => (f i).im
  have ha := hT a
  have hb := hT b
  have habPlus := hT (a + b)
  have habMinus := hT (a - b)
  have hcombined :
      4 * (∑ j, v j * (T a j) ^ 4) +
          4 * (∑ j, v j * (T b j) ^ 4) +
          (∑ j, v j * (T (a + b) j) ^ 4) +
          (∑ j, v j * (T (a - b) j) ^ 4) ≤
        K * (4 * (∑ i, w i * (a i) ^ 4) +
          4 * (∑ i, w i * (b i) ^ 4) +
          (∑ i, w i * ((a + b) i) ^ 4) +
          (∑ i, w i * ((a - b) i) ^ 4)) := by
    linarith only [ha, hb, habPlus, habMinus]
  have hout :
      6 * (∑ j, v j * ((T a j) ^ 2 + (T b j) ^ 2) ^ 2) =
        4 * (∑ j, v j * (T a j) ^ 4) +
          4 * (∑ j, v j * (T b j) ^ 4) +
          (∑ j, v j * (T (a + b) j) ^ 4) +
          (∑ j, v j * (T (a - b) j) ^ 4) := by
    simp_rw [Finset.mul_sum]
    simp_rw [T.map_add, T.map_sub, Pi.add_apply, Pi.sub_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    calc
      6 * (v j * ((T a j) ^ 2 + (T b j) ^ 2) ^ 2) =
          v j * (6 * ((T a j) ^ 2 + (T b j) ^ 2) ^ 2) := by ring
      _ = 4 * (v j * (T a j) ^ 4) + 4 * (v j * (T b j) ^ 4) +
          v j * (T a j + T b j) ^ 4 + v j * (T a j - T b j) ^ 4 := by
        rw [fourth_power_polarization]
        ring
  have hin :
      6 * (∑ i, w i * ((a i) ^ 2 + (b i) ^ 2) ^ 2) =
        4 * (∑ i, w i * (a i) ^ 4) +
          4 * (∑ i, w i * (b i) ^ 4) +
          (∑ i, w i * ((a + b) i) ^ 4) +
          (∑ i, w i * ((a - b) i) ^ 4) := by
    simp_rw [Finset.mul_sum]
    simp_rw [Pi.add_apply, Pi.sub_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      6 * (w i * ((a i) ^ 2 + (b i) ^ 2) ^ 2) =
          w i * (6 * ((a i) ^ 2 + (b i) ^ 2) ^ 2) := by ring
      _ = 4 * (w i * (a i) ^ 4) + 4 * (w i * (b i) ^ 4) +
          w i * (a i + b i) ^ 4 + w i * (a i - b i) ^ 4 := by
        rw [fourth_power_polarization]
        ring
  rw [← hout, ← hin] at hcombined
  have hcancel :
      ∑ j, v j * ((T a j) ^ 2 + (T b j) ^ 2) ^ 2 ≤
        K * ∑ i, w i * ((a i) ^ 2 + (b i) ^ 2) ^ 2 := by
    linarith only [hcombined]
  simpa only [norm_four_eq, coordinatewiseComplexification_re,
    coordinatewiseComplexification_im, a, b] using hcancel

end PDE
