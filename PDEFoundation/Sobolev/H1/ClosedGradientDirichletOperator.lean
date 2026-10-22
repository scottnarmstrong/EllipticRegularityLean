module

public import PDEFoundation.Sobolev.H1.CoefficientGradientCoercivity
public import PDEFoundation.Sobolev.H1.GradientProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The subspace of `L²` vector fields which are zero-boundary gradients. -/
def closedGradientSubspace (hU : IsOpen U) :
    Submodule ℝ (HilbertVectorLp U (2 : ℝ≥0∞)) :=
  LinearMap.range (h10GradientCLM hU).toLinearMap

/-- Restriction of the coefficient energy to zero-boundary gradients. -/
def closedGradientCoefficientBilinear
    (hU : IsOpen U) (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    closedGradientSubspace hU →L[ℝ] closedGradientSubspace hU →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (coefficientGradientBilinear a delta hdelta ha hclose)
    (closedGradientSubspace hU).subtypeL
    (closedGradientSubspace hU).subtypeL

@[simp]
theorem closedGradientCoefficientBilinear_apply
    (hU : IsOpen U) (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g h : closedGradientSubspace hU) :
    closedGradientCoefficientBilinear hU a delta hdelta ha hclose g h =
      inner ℝ (coefficientGradientActionCLM a delta hdelta ha hclose g) h := by
  simp [closedGradientCoefficientBilinear,
    ContinuousLinearMap.bilinearComp_apply]

theorem closedGradientCoefficientBilinear_isCoercive
    (hU : IsOpen U) (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    IsCoercive (closedGradientCoefficientBilinear hU a delta hdelta ha hclose) := by
  refine ⟨1 - delta, sub_pos.mpr hdeltaOne, ?_⟩
  intro g
  rw [closedGradientCoefficientBilinear_apply]
  rw [← Submodule.norm_coe]
  simpa only [pow_two, mul_assoc] using
    one_sub_mul_norm_sq_le_inner_coefficientGradientActionCLM
      a delta hdelta ha hclose (g : HilbertVectorLp U (2 : ℝ≥0∞))

/-- The canonical solution-gradient operator for the zero-boundary equation
with divergence forcing, constructed by Lax--Milgram on the closed gradient
range. -/
def closedGradientDirichletOperator
    (hU : IsOpen U) (C : ℝ)
    (hP : ∀ z : H10Graph hU,
      ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    HilbertVectorLp U (2 : ℝ≥0∞) →L[ℝ] HilbertVectorLp U (2 : ℝ≥0∞) := by
  let S := closedGradientSubspace hU
  have hS : IsClosed (S : Set (HilbertVectorLp U (2 : ℝ≥0∞))) :=
    isClosed_range_h10GradientCLM hU hP
  letI : CompleteSpace S := hS.completeSpace_coe
  let B := closedGradientCoefficientBilinear hU a delta hdelta ha hclose
  let hB : IsCoercive B :=
    closedGradientCoefficientBilinear_isCoercive hU a delta hdelta hdeltaOne ha hclose
  exact S.subtypeL.comp
    (hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
      (-S.subtypeL.adjoint))

theorem closedGradientDirichletOperator_mem_range
    (hU : IsOpen U) (C : ℝ)
    (hP : ∀ z : H10Graph hU,
      ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : HilbertVectorLp U (2 : ℝ≥0∞)) :
    closedGradientDirichletOperator hU C hP a delta hdelta hdeltaOne ha hclose F ∈
      closedGradientSubspace hU := by
  rw [closedGradientDirichletOperator]
  exact Subtype.property _

theorem closedGradientDirichletOperator_weak
    (hU : IsOpen U) (C : ℝ)
    (hP : ∀ z : H10Graph hU,
      ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : HilbertVectorLp U (2 : ℝ≥0∞)) (z : H10Graph hU) :
    inner ℝ
      (coefficientGradientActionCLM a delta hdelta ha hclose
        (closedGradientDirichletOperator hU C hP a delta hdelta hdeltaOne ha hclose F))
      (h10GradientCLM hU z) =
      -inner ℝ F (h10GradientCLM hU z) := by
  let S := closedGradientSubspace hU
  have hS : IsClosed (S : Set (HilbertVectorLp U (2 : ℝ≥0∞))) :=
    isClosed_range_h10GradientCLM hU hP
  let : CompleteSpace S := hS.completeSpace_coe
  let B := closedGradientCoefficientBilinear hU a delta hdelta ha hclose
  let hB : IsCoercive B :=
    closedGradientCoefficientBilinear_isCoercive hU a delta hdelta hdeltaOne ha hclose
  let e : S ≃L[ℝ] S := hB.continuousLinearEquivOfBilin
  let r : S := -(S.subtypeL.adjoint F)
  let q : S := ⟨h10GradientCLM hU z, ⟨z, rfl⟩⟩
  have hop : closedGradientDirichletOperator hU C hP a delta hdelta hdeltaOne ha hclose F =
      (e.symm r : HilbertVectorLp U (2 : ℝ≥0∞)) := by
    rfl
  rw [hop]
  change B (e.symm r) q = -inner ℝ F (S.subtypeL q)
  rw [← hB.continuousLinearEquivOfBilin_apply, e.apply_symm_apply]
  dsimp only [r]
  rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left]

theorem norm_closedGradientDirichletOperator_le
    (hU : IsOpen U) (C : ℝ)
    (hP : ∀ z : H10Graph hU,
      ‖z.1.1.1‖ ≤ C * ‖h10GradientCLM hU z‖)
    (a : CoeffField d) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable
      (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (F : HilbertVectorLp U (2 : ℝ≥0∞)) :
    ‖closedGradientDirichletOperator hU C hP a delta hdelta hdeltaOne ha hclose F‖ ≤
      (1 - delta)⁻¹ * ‖F‖ := by
  let G := closedGradientDirichletOperator hU C hP a delta hdelta hdeltaOne ha hclose F
  have hGmem := closedGradientDirichletOperator_mem_range
    hU C hP a delta hdelta hdeltaOne ha hclose F
  obtain ⟨z, hz⟩ := hGmem
  have hweak := closedGradientDirichletOperator_weak
    hU C hP a delta hdelta hdeltaOne ha hclose F z
  have hz' : h10GradientCLM hU z = G := hz
  rw [hz'] at hweak
  have hcoercive := one_sub_mul_norm_sq_le_inner_coefficientGradientActionCLM
    a delta hdelta ha hclose G
  have hinner : inner ℝ
      (coefficientGradientActionCLM a delta hdelta ha hclose G) G =
      -inner ℝ F G := by simpa only [G] using hweak
  rw [hinner] at hcoercive
  have hcs : -inner ℝ F G ≤ ‖F‖ * ‖G‖ := by
    exact (neg_le_abs _).trans (abs_real_inner_le_norm F G)
  have hmain : (1 - delta) * ‖G‖ * ‖G‖ ≤ ‖F‖ * ‖G‖ := by
    simpa only [pow_two, mul_assoc] using hcoercive.trans hcs
  by_cases hGzero : ‖G‖ = 0
  · simp [G, hGzero, mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hdeltaOne.le)) (norm_nonneg F)]
  · have hGpos : 0 < ‖G‖ := lt_of_le_of_ne (norm_nonneg G) (Ne.symm hGzero)
    have hcancel : (1 - delta) * ‖G‖ ≤ ‖F‖ := by
      nlinarith
    apply (le_inv_mul_iff₀ (sub_pos.mpr hdeltaOne)).2
    exact hcancel

end

end PDE
