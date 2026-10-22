module

public import PDEFoundation.PDE.PerturbationL2
public import PDEFoundation.Sobolev.H1.VectorL2Bounds

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The native representative of a Hilbert-vector `L²` class. -/
def nativeRepresentative (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    Vec d → Vec d := fun x => (g x).toVec

theorem nativeRepresentative_memVectorL2On
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    MemVectorL2On U (nativeRepresentative g) := by
  apply gradMemLpOn_iff_memLp_toHilbertVecField.mpr
  simpa only [nativeRepresentative, toHilbertVecField, Vec.toHilbertVec_toVec]
    using! Lp.memLp g

private theorem nativeRepresentative_toHilbertVectorLp
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    (nativeRepresentative_memVectorL2On g).toHilbertVectorLp = g := by
  apply Lp.ext
  filter_upwards [(nativeRepresentative_memVectorL2On g).coeFn_toHilbertVectorLp]
    with x hx
  simpa only [nativeRepresentative, toHilbertVecField, Vec.toHilbertVec_toVec] using hx

/-- Multiplication of a canonical Hilbert-vector `L²` representative by a
coordinatewise measurable coefficient field close to the identity. -/
def coefficientGradientAction
    (a : CoeffField d) (delta : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    HilbertVectorLp U (2 : ℝ≥0∞) :=
  (memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose
    (nativeRepresentative_memVectorL2On g)).toHilbertVectorLp

/-- The coefficient action agrees almost everywhere with native matrix-vector
multiplication on the canonical representative. -/
theorem coefficientGradientAction_coeFn
    (a : CoeffField d) (delta : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    coefficientGradientAction a delta ha hclose g =ᵐ[volumeOn U]
      fun x => (matVecMul (a x) ((g x).toVec)).toHilbertVec :=
  (memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose
    (nativeRepresentative_memVectorL2On g)).coeFn_toHilbertVectorLp

theorem coefficientGradientAction_add
    (a : CoeffField d) (delta : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g h : HilbertVectorLp U (2 : ℝ≥0∞)) :
    coefficientGradientAction a delta ha hclose (g + h) =
      coefficientGradientAction a delta ha hclose g +
        coefficientGradientAction a delta ha hclose h := by
  apply Lp.ext
  filter_upwards [coefficientGradientAction_coeFn a delta ha hclose (g + h),
    coefficientGradientAction_coeFn a delta ha hclose g,
    coefficientGradientAction_coeFn a delta ha hclose h,
    Lp.coeFn_add g h,
    Lp.coeFn_add (coefficientGradientAction a delta ha hclose g)
      (coefficientGradientAction a delta ha hclose h)] with x hout hg hh hgh hrhs
  rw [hout, hrhs, hgh]
  simp only [Pi.add_apply]
  rw [hg, hh]
  ext i
  simp only [HilbertVec.toVec_apply, Vec.toHilbertVec_apply, WithLp.ofLp_add,
    Pi.add_apply, matVecMul, mul_add, Finset.sum_add_distrib]

theorem coefficientGradientAction_smul
    (a : CoeffField d) (delta : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (c : ℝ) (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    coefficientGradientAction a delta ha hclose (c • g) =
      c • coefficientGradientAction a delta ha hclose g := by
  apply Lp.ext
  filter_upwards [coefficientGradientAction_coeFn a delta ha hclose (c • g),
    coefficientGradientAction_coeFn a delta ha hclose g,
    Lp.coeFn_smul c g,
    Lp.coeFn_smul c (coefficientGradientAction a delta ha hclose g)]
    with x hout hg hcg hrhs
  rw [hout, hrhs, hcg]
  simp only [Pi.smul_apply]
  rw [hg]
  ext i
  simp only [HilbertVec.toVec_apply, Vec.toHilbertVec_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, matVecMul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_coefficientGradientAction_le
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    ‖coefficientGradientAction a delta ha hclose g‖ ≤ (1 + delta) * ‖g‖ := by
  let G := nativeRepresentative g
  let hG : MemVectorL2On U G := nativeRepresentative_memVectorL2On g
  let A : Vec d → Vec d := fun x => matVecMul (a x) (G x)
  let hA : MemVectorL2On U A :=
    memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose hG
  have hbound : ∀ᵐ x ∂volumeOn U,
      vecEuclideanNorm (A x) ≤ (1 + delta) * vecEuclideanNorm (G x) :=
    ae_vecEuclideanNorm_matVecMul_le_one_add_delta_mul_of_isMatrixPerturbationLE hclose
  have hsqrt := sqrt_setIntegral_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    hA hG (by linarith) hbound
  rw [setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hA,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hG,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
  have hAction : hA.toHilbertVectorLp = coefficientGradientAction a delta ha hclose g := rfl
  rw [hAction, nativeRepresentative_toHilbertVectorLp] at hsqrt
  exact hsqrt

/-- The bounded coefficient action on Hilbert-vector `L²`, constructed from
coordinatewise measurability and the actual pointwise perturbation estimate. -/
def coefficientGradientActionCLM
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    HilbertVectorLp U (2 : ℝ≥0∞) →L[ℝ] HilbertVectorLp U (2 : ℝ≥0∞) := by
  let L : HilbertVectorLp U (2 : ℝ≥0∞) →ₗ[ℝ] HilbertVectorLp U (2 : ℝ≥0∞) :=
    { toFun := coefficientGradientAction a delta ha hclose
      map_add' := coefficientGradientAction_add a delta ha hclose
      map_smul' := coefficientGradientAction_smul a delta ha hclose }
  exact L.mkContinuous (1 + delta)
    (norm_coefficientGradientAction_le a delta hdelta ha hclose)

@[simp]
theorem coefficientGradientActionCLM_apply
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    coefficientGradientActionCLM a delta hdelta ha hclose g =
      coefficientGradientAction a delta ha hclose g := rfl

theorem coefficientGradientActionCLM_coeFn
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    coefficientGradientActionCLM a delta hdelta ha hclose g =ᵐ[volumeOn U]
      fun x => (matVecMul (a x) ((g x).toVec)).toHilbertVec := by
  rw [coefficientGradientActionCLM_apply]
  exact coefficientGradientAction_coeFn a delta ha hclose g

theorem norm_coefficientGradientActionCLM_le
    (a : CoeffField d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (g : HilbertVectorLp U (2 : ℝ≥0∞)) :
    ‖coefficientGradientActionCLM a delta hdelta ha hclose g‖ ≤
      (1 + delta) * ‖g‖ :=
  norm_coefficientGradientAction_le a delta hdelta ha hclose g

end

end PDE
