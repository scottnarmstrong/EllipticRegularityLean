module

public import PDEFoundation.Analysis.Newtonian.Matrix.ChangeCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Change of variables in the Newton potential

For `S Sᵀ = M` with `S` invertible and `T = S⁻¹`, the Newton potential of the field
`G(z) = T F(S z)` at `T x` is the matrix potential `newtonPotentialMat M F x`:

* `integral_comp_matVecMul`: `∫ g(S z) dz = |det S|⁻¹ ∫ g`;
* `newtonKernelMat_eq`: `E_M(z) = |det S|⁻¹ (Tᵀ E(T z))`;
* `newtonPotential_transform`: `newtonPotential (T F(S ·)) (T x) = newtonPotentialMat M F x`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem matVecMul_smul (A : Mat d) (c : ℝ) (v : Vec d) :
    matVecMul A (c • v) = c • matVecMul A v := by
  funext i
  simp [matVecMul, Finset.mul_sum, mul_left_comm]

/-- Linear change of variables in the Lebesgue integral. -/
theorem integral_comp_matVecMul {S : Mat d} (hdet : S.det ≠ 0) (g : Vec d → ℝ) :
    ∫ z, g (matVecMul S z) = |S.det|⁻¹ * ∫ u, g u := by
  let e : Vec d ≃ᵐ Vec d :=
    (matHomeomorph (mul_inv_self hdet) (inv_mul_self hdet)).toMeasurableEquiv
  have hf : LinearMap.det (Matrix.mulVecLin S) ≠ 0 := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact hdet
  have hmap : Measure.map e (volume : Measure (Vec d)) =
      ENNReal.ofReal |S.det⁻¹| • (volume : Measure (Vec d)) := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Vec d)) hf
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin'] at this
    exact this
  have h1 := integral_map_equiv e (μ := (volume : Measure (Vec d))) g
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h1
  rw [smul_eq_mul, abs_inv] at h1
  exact h1.symm

theorem newtonKernelMat_eq {M S : Mat d} (hS : S * Sᵀ = M) (z : Vec d) :
    newtonKernelMat M z =
      |S.det|⁻¹ • matVecMul (S⁻¹)ᵀ (newtonKernel (matVecMul S⁻¹ z)) := by
  unfold newtonKernelMat newtonKernel
  have hM : matVecMul (S⁻¹)ᵀ (matVecMul S⁻¹ z) = matVecMul M⁻¹ z := by
    rw [matVecMul_matVecMul, ← inv_eq_transpose_mul hS]
  rw [matVecMul_smul, smul_smul, sqrt_det_eq_abs hS, hM]
  congr 1
  have hq : vecEuclideanNorm (matVecMul S⁻¹ z) ^ d =
      vecDot z (matVecMul M⁻¹ z) ^ ((d : ℝ) / 2) := by
    unfold vecEuclideanNorm
    rw [vecNormSq_inv_matVecMul hS, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
      (by rw [← vecNormSq_inv_matVecMul hS]; exact vecNormSq_nonneg _)]
    congr 1
    ring
  rw [hq]
  simp only [one_div, mul_inv]
  ring

theorem newtonPotential_transform {M S : Mat d} (hS : S * Sᵀ = M) (hdet : S.det ≠ 0)
    (F : Vec d → Vec d) (x : Vec d) :
    newtonPotential (fun z => matVecMul S⁻¹ (F (matVecMul S z))) (matVecMul S⁻¹ x) =
      newtonPotentialMat M F x := by
  have hTS : ∀ v : Vec d, matVecMul S⁻¹ (matVecMul S v) = v := fun v => by
    rw [matVecMul_matVecMul, inv_mul_self hdet, matVecMul_one]
  set g : Vec d → ℝ := fun u =>
    vecDot (newtonKernel (matVecMul S⁻¹ (x - u))) (matVecMul S⁻¹ (F u)) with hg
  have h1 : newtonPotential (fun z => matVecMul S⁻¹ (F (matVecMul S z))) (matVecMul S⁻¹ x) =
      ∫ z, g (matVecMul S z) := by
    unfold newtonPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hg]
    congr 2
    have : matVecMul S⁻¹ (x - matVecMul S z) = matVecMul S⁻¹ x - z := by
      rw [show x - matVecMul S z = x - matVecMul S z from rfl]
      have hsub : ∀ a b : Vec d, matVecMul S⁻¹ (a - b) = matVecMul S⁻¹ a - matVecMul S⁻¹ b := by
        intro a b; funext i; simp [matVecMul, mul_sub, Finset.sum_sub_distrib]
      rw [hsub, hTS]
    rw [this]
  rw [h1, integral_comp_matVecMul hdet, ← integral_const_mul]
  unfold newtonPotentialMat
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hg]
  have key : ∀ a b : Vec d, vecDot a (matVecMul S⁻¹ b) = vecDot (matVecMul (S⁻¹)ᵀ a) b := by
    intro a b
    rw [vecDot_matVecMul_left, Matrix.transpose_transpose]
  have hsm : ∀ (c : ℝ) (a b : Vec d), vecDot (c • a) b = c * vecDot a b := by
    intro c a b
    simp [vecDot, Finset.mul_sum, mul_assoc]
  rw [newtonKernelMat_eq hS, hsm, key]

end MatChange

end PDE
