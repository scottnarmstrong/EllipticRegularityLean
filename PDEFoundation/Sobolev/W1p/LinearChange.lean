module

public import PDEFoundation.Measure.LinearVolume
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.WeakDerivative.Linear
public import PDEFoundation.Sobolev.WeakDerivative.Algebra

/-!
# Weak gradients under an invertible linear change of variables

For `e : Vec d ≃L[ℝ] Vec d` and `v = u ∘ e.symm`, the weak gradient is the
transpose of `e.symm` applied to `Du ∘ e.symm`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

variable {d : ℕ}

/-- The transposed action of a linear equivalence in coordinates:
`(fᵀ z)ᵢ = z ⬝ f eᵢ`. -/
def transposeAction (f : Vec d ≃L[ℝ] Vec d) (z : Vec d) : Vec d :=
  fun i => vecDot z (f (basisVec i))

theorem transposeAction_apply (f : Vec d ≃L[ℝ] Vec d) (z : Vec d) (i : Fin d) :
    transposeAction f z i = vecDot z (f (basisVec i)) :=
  rfl

/-- The defining adjoint identity `(fᵀ z) ⬝ w = z ⬝ f w`. -/
theorem vecDot_transposeAction (f : Vec d ≃L[ℝ] Vec d) (z w : Vec d) :
    vecDot (transposeAction f z) w = vecDot z (f w) := by
  conv_rhs => rw [← sum_smul_basisVec w]
  simp only [vecDot, transposeAction, map_sum, map_smul, Pi.smul_apply,
    smul_eq_mul, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Euclidean operator bounds pass to the transpose. -/
theorem vecEuclideanNorm_transposeAction_le (f : Vec d ≃L[ℝ] Vec d) {L : ℝ}
    (hf : ∀ x, vecEuclideanNorm (f x) ≤ L * vecEuclideanNorm x) (z : Vec d) :
    vecEuclideanNorm (transposeAction f z) ≤ L * vecEuclideanNorm z := by
  set w := transposeAction f z
  have hsq : vecEuclideanNorm w ^ 2 ≤
      (L * vecEuclideanNorm z) * vecEuclideanNorm w := by
    calc vecEuclideanNorm w ^ 2 = vecDot w w := by
          rw [vecEuclideanNorm_sq]; rfl
      _ = vecDot z (f w) := vecDot_transposeAction f z w
      _ ≤ |vecDot z (f w)| := le_abs_self _
      _ ≤ vecEuclideanNorm z * vecEuclideanNorm (f w) :=
          abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ ≤ vecEuclideanNorm z * (L * vecEuclideanNorm w) :=
          mul_le_mul_of_nonneg_left (hf w) (vecEuclideanNorm_nonneg _)
      _ = (L * vecEuclideanNorm z) * vecEuclideanNorm w := by ring
  rcases (vecEuclideanNorm_nonneg w).eq_or_lt with h | h
  · rw [← h]
    by_cases hd : d = 0
    · subst hd
      have : z = 0 := Subsingleton.elim _ _
      rw [this]
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    · have hLnn : 0 ≤ L := by
        have h0 := vecEuclideanNorm_nonneg (f (basisVec ⟨0, Nat.pos_of_ne_zero hd⟩))
        have h1 := hf (basisVec ⟨0, Nat.pos_of_ne_zero hd⟩)
        rw [vecEuclideanNorm_basisVec, mul_one] at h1
        linarith
      exact mul_nonneg hLnn (vecEuclideanNorm_nonneg _)
  · nlinarith

theorem integrable_mul_fderiv_of_locallyIntegrable {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : LocallyIntegrable u (volumeOn U)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (v : Vec d) :
    Integrable (fun x => u x * (fderiv ℝ φ x) v) (volumeOn U) := by
  have hcont : Continuous fun x => (fderiv ℝ φ x) v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcomp : HasCompactSupport fun x => (fderiv ℝ φ x) v :=
    hc.fderiv_apply (𝕜 := ℝ) v
  simpa only [smul_eq_mul] using
    hu.integrable_smul_right_of_hasCompactSupport hcont hcomp

theorem integrable_mul_of_locallyIntegrable {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : LocallyIntegrable u (volumeOn U)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => u x * φ x) (volumeOn U) := by
  simpa only [smul_eq_mul] using
    hu.integrable_smul_right_of_hasCompactSupport
      (hφ.continuous) hc

/-- Pushing a weak gradient forward along a linear equivalence: for
`v = u ∘ e.symm` the weak gradient is `eᵀ`-type action of `Du ∘ e.symm`. -/
theorem HasWeakGradientOn.comp_linearEquiv_symm {U : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du)
    (hu : LocallyIntegrable u (volumeOn U))
    (hDu : ∀ j, LocallyIntegrable (fun x => Du x j) (volumeOn U))
    (e : Vec d ≃L[ℝ] Vec d) :
    HasWeakGradientOn (e '' U) (fun y => u (e.symm y))
      (fun y => transposeAction e.symm (Du (e.symm y))) := by
  intro i φ hφ hc hsub
  let φ' : WeakTestFunction (e '' U) :=
    { toFun := φ, contDiff := hφ, hasCompactSupport := hc, tsupport_subset := hsub }
  let ψ := φ'.compLinearEquiv e
  let J : ℝ := |(LinearMap.det e.toLinearMap)⁻¹|
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det'
  have hJ : 0 < J := abs_pos.mpr (inv_ne_zero hdet)
  have hcoef : ∀ x, (fderiv ℝ φ (e x)) (basisVec i) =
      ∑ j, (e.symm (basisVec i)) j * (fderiv ℝ ψ.toFun x) (basisVec j) := by
    intro x
    have h1 := ContinuousLinearMap.apply_eq_vecDot_basisValues
      ((fderiv ℝ φ (e x)).comp (e : Vec d →L[ℝ] Vec d)) (e.symm (basisVec i))
    have h2 : fderiv ℝ ψ.toFun x = (fderiv ℝ φ (e x)).comp (e : Vec d →L[ℝ] Vec d) :=
      WeakTestFunction.fderiv_compLinearEquiv e φ' x
    have h1' : (fderiv ℝ φ (e x)) (basisVec i) =
        ∑ j, (fderiv ℝ φ (e x)) (e (basisVec j)) * (e.symm (basisVec i)) j := by
      simpa [vecDot] using h1
    rw [h2, h1']
    exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]
  have hint : ∀ j, Integrable (fun x => Du x j * ψ.toFun x) (volumeOn U) := fun j =>
    integrable_mul_of_locallyIntegrable (hDu j) ψ.contDiff ψ.hasCompactSupport
  have hLHS : ∫ x in U, u x * (fderiv ℝ φ (e x)) (basisVec i) =
      -∫ x in U, vecDot (Du x) (e.symm (basisVec i)) * φ (e x) := by
    calc ∫ x in U, u x * (fderiv ℝ φ (e x)) (basisVec i)
        = ∑ j, (e.symm (basisVec i)) j *
            ∫ x in U, u x * (fderiv ℝ ψ.toFun x) (basisVec j) := by
          simp_rw [hcoef, Finset.mul_sum]
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
              simp only; ring)
          · intro j _
            have := integrable_mul_fderiv_of_locallyIntegrable hu ψ.contDiff
              ψ.hasCompactSupport (basisVec j)
            refine (this.const_mul ((e.symm (basisVec i)) j)).congr
              (Filter.Eventually.of_forall fun x => ?_)
            simp only; ring
      _ = ∑ j, (e.symm (basisVec i)) j *
            (-∫ x in U, Du x j * ψ.toFun x) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h j ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset]
      _ = -∫ x in U, vecDot (Du x) (e.symm (basisVec i)) * φ (e x) := by
          have : ∫ x in U, vecDot (Du x) (e.symm (basisVec i)) * φ (e x) =
              ∑ j, (e.symm (basisVec i)) j * ∫ x in U, Du x j * ψ.toFun x := by
            simp_rw [← integral_const_mul]
            rw [← integral_finsetSum]
            · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              simp only [vecDot, Finset.sum_mul, WeakTestFunction.compLinearEquiv_apply, ψ, φ']
              exact Finset.sum_congr rfl fun j _ => by
                ring
            · intro j _
              exact (hint j).const_mul _
          rw [this, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hA := setIntegral_comp_linearEquiv e U
    (fun y => u (e.symm y) * (fderiv ℝ φ y) (basisVec i))
  have hB := setIntegral_comp_linearEquiv e U
    (fun y => transposeAction e.symm (Du (e.symm y)) i * φ y)
  simp only [ContinuousLinearEquiv.symm_apply_apply, transposeAction_apply] at hA hB
  change _ = J • _ at hA
  change _ = J • _ at hB
  rw [hLHS] at hA
  have hB' : ∫ x in U, vecDot (Du x) (e.symm (basisVec i)) * φ (e x) =
      J * ∫ y in e '' U, transposeAction e.symm (Du (e.symm y)) i * φ y := by
    simpa only [transposeAction_apply, smul_eq_mul] using hB
  rw [hB'] at hA
  simp only [smul_eq_mul] at hA
  have hA' : J * (∫ y in e '' U, u (e.symm y) * (fderiv ℝ φ y) (basisVec i)) =
      J * (-∫ y in e '' U, transposeAction e.symm (Du (e.symm y)) i * φ y) := by
    rw [← hA]; ring
  exact mul_left_cancel₀ hJ.ne' hA'

end PDE
