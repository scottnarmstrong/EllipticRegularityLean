module

public import PDEFoundation.Ambient.MatrixLinearEquiv
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.Linear

/-!
# Linear changes of variables in divergence-form equations

This module transports the actual smooth-test weak formulation through an
arbitrary invertible constant matrix, with the determinant factor cancelled
explicitly on all three terms.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem matVecMul_mul (A B : Mat d) (v : Vec d) :
    matVecMul (A * B) v = matVecMul A (matVecMul B v) := by
  change (A * B).mulVec v = A.mulVec (B.mulVec v)
  exact (Matrix.mulVec_mulVec v A B).symm

private theorem matVecMul_one (v : Vec d) :
    matVecMul (1 : Mat d) v = v := by
  exact Matrix.one_mulVec v

private theorem vecDot_matVecMul_eq_vecDot_matTranspose
    (A : Mat d) (v w : Vec d) :
    vecDot (matVecMul A v) w = vecDot v (matVecMul (matTranspose A) w) := by
  unfold vecDot matVecMul matTranspose
  simp only [Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem transpose_mul_transpose_inv_eq_one
    (T : Mat d) (hT : IsUnit T) :
    matTranspose T * matTranspose T⁻¹ = 1 := by
  change T.transpose * T⁻¹.transpose = 1
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul T
    (T.isUnit_iff_isUnit_det.mp hT)]
  ext i j
  by_cases hij : i = j
  · simp [Matrix.one_apply, hij]
  · simp [hij, Ne.symm hij]

private theorem transformedGradient_at_image
    (T : Mat d) (hT : IsUnit T) {U : Set (Vec d)}
    (u : H1Function U) (x : Vec d) :
    (u.compLinearEquiv (matrixContinuousLinearEquiv T hT)).grad
        (matrixContinuousLinearEquiv T hT x) =
      matVecMul (matTranspose T⁻¹) (u.grad x) := by
  ext i
  simp only [H1Function.compLinearEquiv_grad_apply,
    matrixContinuousLinearEquiv_symm_apply,
    matrixContinuousLinearEquiv_apply]
  have hx : matVecMul T⁻¹ (matVecMul T x) = x := by
    rw [← matVecMul_mul, Matrix.nonsing_inv_mul T
      (T.isUnit_iff_isUnit_det.mp hT), matVecMul_one]
  rw [hx]
  unfold vecDot matTranspose
  apply Finset.sum_congr rfl
  intro j _hj
  have hbasis : matVecMul T⁻¹ (basisVec i) j = T⁻¹ j i := by
    simp [matVecMul, basisVec_apply]
  rw [hbasis]
  change u.grad x j * T⁻¹ j i = T⁻¹ j i * u.grad x j
  ring

private theorem pulledTestGradient
    (T : Mat d) (hT : IsUnit T) {U : Set (Vec d)}
    (φ : WeakTestFunction
      (matrixContinuousLinearEquiv T hT '' U)) (x : Vec d) :
    (φ.compLinearEquiv (matrixContinuousLinearEquiv T hT)).grad x =
      matVecMul (matTranspose T)
        (φ.grad (matrixContinuousLinearEquiv T hT x)) := by
  ext j
  change (φ.compLinearEquiv (matrixContinuousLinearEquiv T hT)).partialDeriv j x =
    matVecMul (matTranspose T)
      (fun i => φ.partialDeriv i (matrixContinuousLinearEquiv T hT x)) j
  simp only [WeakTestFunction.partialDeriv]
  rw [WeakTestFunction.fderiv_compLinearEquiv]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, matrixContinuousLinearEquiv_apply]
  rw [PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues]
  unfold vecDot matVecMul matTranspose basisVec
  simp only [Matrix.transpose_apply, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  have hbasis : ∑ k, T i k * (if k = j then 1 else 0) = T i j := by
    simp
  rw [hbasis]
  ring

private theorem transformedFlux_at_image
    (T : Mat d) (hT : IsUnit T) {a : CoeffField d}
    {U : Set (Vec d)} (u : H1Function U) (x : Vec d) :
    matVecMul
        (T * a x * matTranspose T)
        ((u.compLinearEquiv (matrixContinuousLinearEquiv T hT)).grad
          (matrixContinuousLinearEquiv T hT x)) =
      matVecMul T (matVecMul (a x) (u.grad x)) := by
  rw [transformedGradient_at_image]
  have hcancel : matVecMul (matTranspose T)
      (matVecMul (matTranspose T⁻¹) (u.grad x)) = u.grad x := by
    calc
      matVecMul (matTranspose T)
          (matVecMul (matTranspose T⁻¹) (u.grad x)) =
          matVecMul (matTranspose T * matTranspose T⁻¹) (u.grad x) :=
        (matVecMul_mul _ _ _).symm
      _ = u.grad x := by
        rw [transpose_mul_transpose_inv_eq_one T hT, matVecMul_one]
  rw [matVecMul_mul, matVecMul_mul, hcancel]

private theorem integrableOn_of_comp_linearEquiv
    {U : Set (Vec d)} (e : Vec d ≃L[ℝ] Vec d) {f : Vec d → ℝ}
    (hf : IntegrableOn (fun x => f (e x)) U volume) :
    IntegrableOn f (e '' U) volume := by
  have hmap : Integrable f (Measure.map e (volumeOn U)) :=
    e.toHomeomorph.measurableEmbedding.integrable_map_iff.mpr hf
  rw [map_linearEquiv_volumeOn] at hmap
  have hc0 : ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr
      (inv_ne_zero (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')))).ne'
  exact (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).mp hmap

/-- Transport an actual divergence-form weak solution through an invertible
constant matrix. -/
theorem IsWeakDivergenceFormSolutionOn.linearChange
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {F : Vec d → Vec d}
    (T : Mat d) (hT : IsUnit T)
    (hu : IsWeakDivergenceFormSolutionOn a U u f F) :
    let e := matrixContinuousLinearEquiv T hT
    IsWeakDivergenceFormSolutionOn
      (fun y => T * a (e.symm y) * matTranspose T)
      (e '' U) (u.compLinearEquiv e)
      (fun y => f (e.symm y))
      (fun y => matVecMul T (F (e.symm y))) := by
  let e := matrixContinuousLinearEquiv T hT
  dsimp only
  intro φ
  let ψ : WeakTestFunction U := φ.compLinearEquiv e
  have hold := hu ψ
  have hfluxPoint : ∀ x,
      vecDot
          (matVecMul (T * a x * matTranspose T)
            ((u.compLinearEquiv e).grad (e x)))
          (φ.grad (e x)) =
        vecDot (matVecMul (a x) (u.grad x)) (ψ.grad x) := by
    intro x
    rw [show e = matrixContinuousLinearEquiv T hT from rfl,
      transformedFlux_at_image T hT u x,
      show ψ.grad x = matVecMul (matTranspose T) (φ.grad (e x)) by
        exact pulledTestGradient T hT φ x]
    exact vecDot_matVecMul_eq_vecDot_matTranspose T _ _
  have hforcingPoint : ∀ x,
      vecDot (matVecMul T (F x)) (φ.grad (e x)) =
        vecDot (F x) (ψ.grad x) := by
    intro x
    rw [show ψ.grad x = matVecMul (matTranspose T) (φ.grad (e x)) by
      exact pulledTestGradient T hT φ x]
    exact vecDot_matVecMul_eq_vecDot_matTranspose T _ _
  have hfluxComp : IntegrableOn
      (fun x => vecDot
        (matVecMul (T * a x * matTranspose T)
          ((u.compLinearEquiv e).grad (e x)))
        (φ.grad (e x))) U volume :=
    hold.1.flux_integrable.congr
      (Filter.Eventually.of_forall fun x => (hfluxPoint x).symm)
  have hsourceComp : IntegrableOn
      (fun x => f x * φ (e x)) U volume := by
    simpa only [ψ, WeakTestFunction.compLinearEquiv_apply] using
      hold.1.source_integrable
  have hforcingComp : IntegrableOn
      (fun x => vecDot (matVecMul T (F x)) (φ.grad (e x))) U volume :=
    hold.1.forcing_integrable.congr
      (Filter.Eventually.of_forall fun x => (hforcingPoint x).symm)
  have hfluxInt := integrableOn_of_comp_linearEquiv (e := e)
    (f := fun y => vecDot
      (matVecMul (T * a (e.symm y) * matTranspose T)
        ((u.compLinearEquiv e).grad y)) (φ.grad y)) (by
      simpa only [e.symm_apply_apply] using hfluxComp)
  have hsourceInt := integrableOn_of_comp_linearEquiv (e := e)
    (f := fun y => f (e.symm y) * φ y) (by
      simpa only [e.symm_apply_apply] using hsourceComp)
  have hforcingInt := integrableOn_of_comp_linearEquiv (e := e)
    (f := fun y => vecDot (matVecMul T (F (e.symm y))) (φ.grad y)) (by
      simpa only [e.symm_apply_apply] using hforcingComp)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [e, matrixContinuousLinearEquiv_symm_apply,
      matrixContinuousLinearEquiv_apply] using hfluxInt
  · simpa only [e, matrixContinuousLinearEquiv_symm_apply,
      matrixContinuousLinearEquiv_apply] using hsourceInt
  · simpa only [e, matrixContinuousLinearEquiv_symm_apply,
      matrixContinuousLinearEquiv_apply] using hforcingInt
  · let J : ℝ := |(LinearMap.det e.toLinearMap)⁻¹|
    have hJ : J ≠ 0 := by
      apply abs_ne_zero.mpr
      exact inv_ne_zero (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')
    have hfluxChange := setIntegral_comp_linearEquiv e U
      (fun y => vecDot
        (matVecMul (T * a (e.symm y) * matTranspose T)
          ((u.compLinearEquiv e).grad y)) (φ.grad y))
    have hsourceChange := setIntegral_comp_linearEquiv e U
      (fun y => f (e.symm y) * φ y)
    have hforcingChange := setIntegral_comp_linearEquiv e U
      (fun y => vecDot (matVecMul T (F (e.symm y))) (φ.grad y))
    have hfluxChange' :
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (ψ.grad x) ∂volume) =
          J * ∫ y in e '' U, vecDot
            (matVecMul (T * a (e.symm y) * matTranspose T)
              ((u.compLinearEquiv e).grad y)) (φ.grad y) ∂volume := by
      rw [← integral_congr_ae (Filter.Eventually.of_forall hfluxPoint)]
      simpa only [J, e.symm_apply_apply, smul_eq_mul] using hfluxChange
    have hsourceChange' :
        (∫ x in U, f x * ψ x ∂volume) =
          J * ∫ y in e '' U, f (e.symm y) * φ y ∂volume := by
      simpa only [ψ, WeakTestFunction.compLinearEquiv_apply, J,
        e.symm_apply_apply, smul_eq_mul] using hsourceChange
    have hforcingChange' :
        (∫ x in U, vecDot (F x) (ψ.grad x) ∂volume) =
          J * ∫ y in e '' U,
            vecDot (matVecMul T (F (e.symm y))) (φ.grad y) ∂volume := by
      rw [← integral_congr_ae (Filter.Eventually.of_forall hforcingPoint)]
      simpa only [J, e.symm_apply_apply, smul_eq_mul] using hforcingChange
    apply mul_left_cancel₀ hJ
    rw [← hfluxChange', hold.2, hsourceChange', hforcingChange']
    ring

end

end PDE
