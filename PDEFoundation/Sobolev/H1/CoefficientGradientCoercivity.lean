module

public import PDEFoundation.Sobolev.H1.CoefficientGradientAction
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

@[expose] public section

open scoped ENNReal RealInnerProductSpace

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private theorem nativeRepresentative_toHilbertVectorLp
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    (nativeRepresentative_memVectorL2On g).toHilbertVectorLp = g := by
  apply Lp.ext
  filter_upwards [(nativeRepresentative_memVectorL2On g).coeFn_toHilbertVectorLp]
    with x hx
  simpa only [nativeRepresentative, toHilbertVecField, Vec.toHilbertVec_toVec] using hx

/-- The coefficient action has the integrated lower bound inherited from its
pointwise perturbation bound. This remains valid when `delta ≥ 1`. -/
theorem one_sub_mul_norm_sq_le_inner_coefficientGradientActionCLM
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    (1 - delta) * ‖g‖ ^ 2 ≤
      inner ℝ (coefficientGradientActionCLM a delta hdelta ha hclose g) g := by
  let G : Vec d → Vec d := nativeRepresentative g
  let A : Vec d → Vec d := fun x => matVecMul (a x) (G x)
  let hG : MemVectorL2On U G := nativeRepresentative_memVectorL2On g
  let hA : MemVectorL2On U A :=
    memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose hG
  have hpoint : ∀ᵐ x ∂volumeOn U,
      (1 - delta) * vecNormSq (G x) ≤ vecDot (A x) (G x) := by
    filter_upwards [hclose] with x hx
    simpa only [A, G, vecDot_comm] using
      one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
        hx (G x)
  have hintegral :
      (1 - delta) * ∫ x in U, vecNormSq (G x) ≤
        ∫ x in U, vecDot (A x) (G x) := by
    rw [← integral_const_mul]
    exact integral_mono_ae
      ((integrableOn_vecNormSq_of_memVectorL2On hG).const_mul (1 - delta))
      (integrableOn_vecDot_of_memVectorL2On hA hG) hpoint
  rw [setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hG] at hintegral
  have hclassG : hG.toHilbertVectorLp = g :=
    nativeRepresentative_toHilbertVectorLp g
  have hclassA : hA.toHilbertVectorLp =
      coefficientGradientActionCLM a delta hdelta ha hclose g := rfl
  have hpair := setIntegral_vecDot_eq_inner_of_ae_eq
    hA.toHilbertVectorLp hG.toHilbertVectorLp A G
    hA.coeFn_toHilbertVectorLp hG.coeFn_toHilbertVectorLp
  rw [hpair, hclassA, hclassG] at hintegral
  exact hintegral

/-- The coefficient energy as an actual bounded bilinear form on vector `L²`. -/
def coefficientGradientBilinear
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    HilbertVectorLp U (2 : ℝ≥0∞) →L[ℝ]
      HilbertVectorLp U (2 : ℝ≥0∞) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (coefficientGradientActionCLM a delta hdelta ha hclose)
    (ContinuousLinearMap.id ℝ _)

@[simp]
theorem coefficientGradientBilinear_apply
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g h : HilbertVectorLp U (2 : ℝ≥0∞)) :
    coefficientGradientBilinear a delta hdelta ha hclose g h =
      inner ℝ (coefficientGradientActionCLM a delta hdelta ha hclose g) h := by
  simp [coefficientGradientBilinear, ContinuousLinearMap.bilinearComp_apply]

/-- For `delta < 1`, the coefficient energy is coercive with the explicit
constant `1 - delta`. -/
theorem coefficientGradientBilinear_isCoercive
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    IsCoercive (coefficientGradientBilinear a delta hdelta ha hclose) := by
  refine ⟨1 - delta, sub_pos.mpr hdeltaOne, ?_⟩
  intro g
  rw [coefficientGradientBilinear_apply]
  convert one_sub_mul_norm_sq_le_inner_coefficientGradientActionCLM
    a delta hdelta ha hclose g using 1
  ring

end

end PDE
