module

public import PDEFoundation.Analysis.Newtonian.Matrix.ChangePotential
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Scaling of the Newton potential and linear images of sets

For `R > 0` the field `z ↦ R • G (R • z)` has Newton potential `y ↦ u_G (R • y)`, hence gradient
`R • ∇u_G (R • y)`.  We also record the volume of the image of a set under `matVecMul A`, and
two elementary topological facts about supports and Euclidean balls under dilation.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem matVecMul_scalar (R : ℝ) (v : Vec d) : matVecMul (R • (1 : Mat d)) v = R • v := by
  funext i
  simp [matVecMul, Matrix.smul_apply, Matrix.one_apply]

theorem det_scalar (R : ℝ) : (R • (1 : Mat d)).det = R ^ d := by
  simp

theorem newtonKernel_smul {R : ℝ} (hR : 0 < R) (v : Vec d) :
    newtonKernel (R • v) = (R / R ^ d) • newtonKernel v := by
  unfold newtonKernel
  simp only [smul_smul]
  rw [vecEuclideanNorm_smul, abs_of_pos hR, mul_pow]
  congr 1
  have hR' : (R : ℝ) ≠ 0 := hR.ne'
  have hRd : R ^ d ≠ 0 := pow_ne_zero _ hR'
  by_cases hv : vecEuclideanNorm v ^ d = 0
  · rw [hv]; simp
  · field_simp

/-- The potential of the dilated field is the dilated potential. -/
theorem newtonPotential_dilate {R : ℝ} (hR : 0 < R) (G : Vec d → Vec d) (y : Vec d) :
    newtonPotential (fun z => R • G (R • z)) y = newtonPotential G (R • y) := by
  have hdet : (R • (1 : Mat d)).det ≠ 0 := by
    rw [det_scalar]; exact pow_ne_zero _ hR.ne'
  have h1 := integral_comp_matVecMul hdet
    (fun w => vecDot (newtonKernel (R • y - w)) (G w))
  simp only [matVecMul_scalar, det_scalar] at h1
  have hRd : (0 : ℝ) < R ^ d := pow_pos hR d
  have h2 : newtonPotential G (R • y) = R ^ d * ∫ z, vecDot (newtonKernel (R • y - R • z)) (G (R • z)) := by
    rw [h1, abs_of_pos hRd, ← mul_assoc, mul_inv_cancel₀ hRd.ne', one_mul]
    rfl
  have hsm : ∀ (c : ℝ) (a b : Vec d), vecDot (c • a) b = c * vecDot a b := by
    intro c a b
    simp [vecDot, Finset.mul_sum, mul_assoc]
  have hsm' : ∀ (c : ℝ) (a b : Vec d), vecDot a (c • b) = c * vecDot a b := by
    intro c a b
    simp [vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  unfold newtonPotential
  have : ∀ z : Vec d, vecDot (newtonKernel (R • y - R • z)) (G (R • z)) =
      (R / R ^ d) * vecDot (newtonKernel (y - z)) (G (R • z)) := by
    intro z
    rw [← smul_sub, newtonKernel_smul hR, hsm]
  simp only [this, hsm', integral_const_mul]
  field_simp

theorem classicalGradient_newtonPotential_dilate {R : ℝ} (hR : 0 < R)
    {G : Vec d → Vec d} (y : Vec d)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (newtonPotential G)) :
    classicalGradient (newtonPotential (fun z => R • G (R • z))) y =
      R • classicalGradient (newtonPotential G) (R • y) := by
  have e : newtonPotential (fun z => R • G (R • z)) =
      fun y => newtonPotential G (matVecMul (R • (1 : Mat d)) y) := by
    funext y
    rw [newtonPotential_dilate hR, matVecMul_scalar]
  rw [e, classicalGradient_comp_matVecMul _ hu, matVecMul_scalar]
  have : (R • (1 : Mat d))ᵀ = R • (1 : Mat d) := by simp
  rw [this, matVecMul_scalar]

theorem volume_image_matVecMul (A : Mat d) (s : Set (Vec d)) :
    volume ((fun y => matVecMul A y) '' s) = ENNReal.ofReal |A.det| * volume s := by
  have hf := Measure.addHaar_image_linearMap (volume : Measure (Vec d)) (Matrix.mulVecLin A) s
  rw [← Matrix.toLin'_apply', LinearMap.det_toLin'] at hf
  exact hf

theorem tsupport_subset_preimage {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Zero β] [Zero γ] {φ : α → α} (hφ : Continuous φ) {f : α → β} {g : α → γ}
    (h : Function.support g ⊆ φ ⁻¹' Function.support f) :
    tsupport g ⊆ φ ⁻¹' tsupport f := by
  exact (closure_mono h).trans (hφ.closure_preimage_subset _)

end MatChange

end PDE
