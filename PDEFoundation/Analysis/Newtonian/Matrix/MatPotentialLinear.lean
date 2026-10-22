module

public import PDEFoundation.Analysis.Newtonian.Matrix.ChangePotential
public import PDEFoundation.Analysis.Newtonian.Potential.Decay
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability and linearity of the matrix Newton potential

For continuous compactly supported `F`, the integrand of `newtonPotentialMat M F x` is integrable
(by the change of variables to the Laplacian kernel), hence `F ↦ newtonPotentialMat M F` is linear
on such fields.  Scalar homogeneity needs no hypotheses.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem newtonPotentialMat_smul (M : Mat d) (c : ℝ) (F : Vec d → Vec d) :
    newtonPotentialMat M (c • F) = c • newtonPotentialMat M F := by
  funext x
  unfold newtonPotentialMat
  rw [Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [vecDot, Finset.mul_sum, mul_left_comm]

/-- Integrability transfers along an invertible linear change of variables. -/
theorem integrable_of_comp_matVecMul {S : Mat d} (hdet : S.det ≠ 0) {g : Vec d → ℝ}
    (hg : Integrable fun z => g (matVecMul S z)) : Integrable g := by
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
  have h1 : Integrable g (Measure.map e (volume : Measure (Vec d))) :=
    (integrable_map_equiv e g).2 hg
  rw [hmap] at h1
  have hne : ENNReal.ofReal |S.det⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (inv_ne_zero hdet)
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 h1

theorem integrand_comp_matVecMul {M S : Mat d} (hS : S * Sᵀ = M) (hdet : S.det ≠ 0)
    (F : Vec d → Vec d) (x z : Vec d) :
    vecDot (newtonKernelMat M (x - matVecMul S z)) (F (matVecMul S z)) =
      |S.det|⁻¹ * vecDot (newtonKernel (matVecMul S⁻¹ x - z))
        (matVecMul S⁻¹ (F (matVecMul S z))) := by
  have hTS : ∀ v : Vec d, matVecMul S⁻¹ (matVecMul S v) = v := fun v => by
    rw [matVecMul_matVecMul, inv_mul_self hdet, matVecMul_one]
  have hsub : ∀ a b : Vec d, matVecMul S⁻¹ (a - b) = matVecMul S⁻¹ a - matVecMul S⁻¹ b := by
    intro a b; funext i; simp [matVecMul, mul_sub, Finset.sum_sub_distrib]
  have key : ∀ a b : Vec d, vecDot a (matVecMul S⁻¹ b) = vecDot (matVecMul (S⁻¹)ᵀ a) b := by
    intro a b
    rw [vecDot_matVecMul_left, Matrix.transpose_transpose]
  have hsm : ∀ (c : ℝ) (a b : Vec d), vecDot (c • a) b = c * vecDot a b := by
    intro c a b
    simp [vecDot, Finset.mul_sum, mul_assoc]
  rw [newtonKernelMat_eq hS, hsm, hsub, hTS, key]

/-- The integrand of `newtonPotentialMat M F x` is integrable. -/
theorem integrable_vecDot_newtonKernelMat_sub (hd : 0 < d) {M S : Mat d} (hS : S * Sᵀ = M)
    (hdet : S.det ≠ 0) {F : Vec d → Vec d} (hF : Continuous F) (hFc : HasCompactSupport F)
    (x : Vec d) :
    Integrable fun y => vecDot (newtonKernelMat M (x - y)) (F y) := by
  refine integrable_of_comp_matVecMul hdet ?_
  have hG : Continuous fun z => matVecMul S⁻¹ (F (matVecMul S z)) :=
    (continuous_matVecMul _).comp (hF.comp (continuous_matVecMul _))
  have hGc : HasCompactSupport fun z => matVecMul S⁻¹ (F (matVecMul S z)) :=
    hasCompactSupport_matVecMul_comp hdet hFc
  have := (integrable_vecDot_newtonKernel_sub hd hG hGc (matVecMul S⁻¹ x)).const_mul |S.det|⁻¹
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  exact (integrand_comp_matVecMul hS hdet F x z).symm

theorem vecDot_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → ℝ) (a : Vec d) (v : ι → Vec d) :
    vecDot a (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * vecDot a (v i) := by
  simp only [vecDot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- Linearity of the Laplacian Newton potential on continuous compactly supported fields. -/
theorem newtonPotential_linearCombination {ι : Type*} (hd : 0 < d) (s : Finset ι) (c : ι → ℝ)
    (F : ι → Vec d → Vec d) (hF : ∀ i ∈ s, Continuous (F i))
    (hFc : ∀ i ∈ s, HasCompactSupport (F i)) :
    newtonPotential (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • newtonPotential (F i) := by
  funext x
  have e : ∀ y, (∑ i ∈ s, c i • F i) y = ∑ i ∈ s, c i • F i y := fun y => by
    simp [Finset.sum_apply]
  unfold newtonPotential
  simp only [e, vecDot_sum_smul_right, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ fun i hi => (integrable_vecDot_newtonKernel_sub hd (hF i hi) (hFc i hi)
    x).const_mul (c i)]
  simp only [integral_const_mul]

/-- Linearity of the matrix Newton potential on continuous compactly supported fields. -/
theorem newtonPotentialMat_linearCombination {ι : Type*} (hd : 0 < d) {M S : Mat d}
    (hS : S * Sᵀ = M) (hdet : S.det ≠ 0) (s : Finset ι) (c : ι → ℝ)
    (F : ι → Vec d → Vec d) (hF : ∀ i ∈ s, Continuous (F i))
    (hFc : ∀ i ∈ s, HasCompactSupport (F i)) :
    newtonPotentialMat M (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • newtonPotentialMat M (F i) := by
  funext x
  have e : ∀ y, (∑ i ∈ s, c i • F i) y = ∑ i ∈ s, c i • F i y := fun y => by
    simp [Finset.sum_apply]
  unfold newtonPotentialMat
  simp only [e, vecDot_sum_smul_right, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ fun i hi =>
    (integrable_vecDot_newtonKernelMat_sub hd hS hdet (hF i hi) (hFc i hi) x).const_mul (c i)]
  simp only [integral_const_mul]

end MatChange

end PDE
