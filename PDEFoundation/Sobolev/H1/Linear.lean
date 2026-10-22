module

public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.WeakDerivative.Linear

/-!
# Linear transport of representative-level `H¹` functions

An invertible linear change of variables transports both the chosen value
representative and the exact native coordinate gradient.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

namespace H1Function

private theorem integral_mul_fderiv_apply_eq_neg_integral_vecDot
    (u : H1Function U) (φ : WeakTestFunction U) (z : Vec d) :
    (∫ x in U, u x * (fderiv ℝ φ.toFun x) z ∂volume) =
      -∫ x in U, vecDot (u.grad x) z * φ x ∂volume := by
  have hleftInt : ∀ j : Fin d,
      IntegrableOn
        (fun x => u x * (z j * φ.partialDeriv j x)) U volume := by
    intro j
    have hbase := integrableOn_mul_of_memL2On u.memL2
      (φ.memLp_partialDeriv j 2)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using! hbase.mul_const (z j)
  have hrightInt : ∀ j : Fin d,
      IntegrableOn
        (fun x => (z j * u.grad x j) * φ x) U volume := by
    intro j
    have hbase := integrableOn_mul_of_memL2On (u.gradMemL2 j) φ.memL2On
    simpa only [mul_assoc, mul_comm, mul_left_comm] using! hbase.mul_const (z j)
  have hcoord : ∀ j : Fin d,
      (∫ x in U, u x * (z j * φ.partialDeriv j x) ∂volume) =
        -∫ x in U, (z j * u.grad x j) * φ x ∂volume := by
    intro j
    have hj := (hasWeakPartialDerivOn_iff_forall_testFunction.mp
      (u.hasWeakGradient j)) φ
    calc
      (∫ x in U, u x * (z j * φ.partialDeriv j x) ∂volume) =
          z j * ∫ x in U, u x * φ.partialDeriv j x ∂volume := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = z j * (-∫ x in U, u.grad x j * φ x ∂volume) := by rw [hj]
      _ = -∫ x in U, (z j * u.grad x j) * φ x ∂volume := by
        calc
          z j * (-∫ x in U, u.grad x j * φ x ∂volume) =
              -(z j * ∫ x in U, u.grad x j * φ x ∂volume) := by ring
          _ = -∫ x in U, z j * (u.grad x j * φ x) ∂volume := by
            rw [integral_const_mul]
          _ = -∫ x in U, (z j * u.grad x j) * φ x ∂volume := by
            apply congrArg Neg.neg
            apply integral_congr_ae
            filter_upwards with x
            ring
  have hderiv : ∀ x,
      (fderiv ℝ φ.toFun x) z =
        ∑ j : Fin d, z j * φ.partialDeriv j x := by
    intro x
    rw [PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues]
    unfold vecDot WeakTestFunction.partialDeriv
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc
    (∫ x in U, u x * (fderiv ℝ φ.toFun x) z ∂volume) =
        ∫ x in U, ∑ j : Fin d,
          u x * (z j * φ.partialDeriv j x) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hderiv]
      rw [Finset.mul_sum]
    _ = ∑ j : Fin d,
        ∫ x in U, u x * (z j * φ.partialDeriv j x) ∂volume := by
      rw [integral_finsetSum Finset.univ (fun j _ => hleftInt j)]
    _ = ∑ j : Fin d,
        (-∫ x in U, (z j * u.grad x j) * φ x ∂volume) := by
      exact Finset.sum_congr rfl fun j _ => hcoord j
    _ = -∫ x in U, vecDot (u.grad x) z * φ x ∂volume := by
      rw [Finset.sum_neg_distrib,
        ← integral_finsetSum Finset.univ (fun j _ => hrightInt j)]
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards with x
      unfold vecDot
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

theorem memL2On_comp_symm
    (e : Vec d ≃L[ℝ] Vec d) {f : Vec d → ℝ} (hf : MemL2On U f) :
    MemL2On (e '' U) (fun x => f (e.symm x)) := by
  have himage : e.symm '' (e '' U) = U := by
    ext x
    constructor
    · rintro ⟨_y, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  rw [← himage] at hf
  exact memLpOn_comp_linearEquiv e.symm hf

theorem gradCoord_comp_symm_memL2
    (e : Vec d ≃L[ℝ] Vec d) (u : H1Function U) (i : Fin d) :
    MemL2On (e '' U)
      (fun x => vecDot (u.grad (e.symm x)) (e.symm (basisVec i))) := by
  unfold vecDot
  apply memLp_finsetSum Finset.univ
  intro j _hj
  have hj : MemL2On (e '' U) (fun x => u.grad (e.symm x) j) :=
    memL2On_comp_symm e (u.gradMemL2 j)
  simpa only [mul_comm] using hj.mul_const (e.symm (basisVec i) j)

/-- The weak gradient transforms by the transpose inverse, expressed without
introducing a competing matrix or ambient-space API. -/
theorem hasWeakGradient_compLinearEquiv
    (e : Vec d ≃L[ℝ] Vec d) (u : H1Function U) :
    HasWeakGradientOn (e '' U)
      (fun x => u (e.symm x))
      (fun x i => vecDot (u.grad (e.symm x)) (e.symm (basisVec i))) := by
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro φ
  let ψ : WeakTestFunction U := φ.compLinearEquiv e
  let z : Vec d := e.symm (basisVec i)
  have hdir := integral_mul_fderiv_apply_eq_neg_integral_vecDot u ψ z
  have hderiv : ∀ y,
      (fderiv ℝ ψ.toFun y) z = (fderiv ℝ φ.toFun (e y)) (basisVec i) :=
    fun y => WeakTestFunction.fderiv_compLinearEquiv_apply_symm_basisVec e φ y i
  have hdir' :
      (∫ y in U, u y * (fderiv ℝ φ.toFun (e y)) (basisVec i) ∂volume) =
        -∫ y in U, vecDot (u.grad y) z * φ (e y) ∂volume := by
    simpa only [ψ, z, WeakTestFunction.compLinearEquiv_apply, hderiv] using hdir
  let J : ℝ := |(LinearMap.det e.toLinearMap)⁻¹|
  have hJ : J ≠ 0 := by
    apply abs_ne_zero.mpr
    exact inv_ne_zero (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')
  have hleft := setIntegral_comp_linearEquiv e U
    (fun x => u (e.symm x) * (fderiv ℝ φ.toFun x) (basisVec i))
  have hright := setIntegral_comp_linearEquiv e U
    (fun x => vecDot (u.grad (e.symm x)) z * φ x)
  have hleft' :
      (∫ x in U, u x * (fderiv ℝ φ.toFun (e x)) (basisVec i) ∂volume) =
        J * ∫ x in e '' U,
          u (e.symm x) * (fderiv ℝ φ.toFun x) (basisVec i) ∂volume := by
    simpa only [J, e.symm_apply_apply, smul_eq_mul] using hleft
  have hright' :
      (∫ x in U, vecDot (u.grad x) z * φ (e x) ∂volume) =
        J * ∫ x in e '' U,
          vecDot (u.grad (e.symm x)) z * φ x ∂volume := by
    simpa only [J, e.symm_apply_apply, smul_eq_mul] using hright
  have hscaled :
      J * (∫ x in e '' U,
        u (e.symm x) * (fderiv ℝ φ.toFun x) (basisVec i) ∂volume) =
        J * (-∫ x in e '' U,
          vecDot (u.grad (e.symm x)) z * φ x ∂volume) := by
    rw [← hleft']
    calc
      (∫ x in U, u x * (fderiv ℝ φ.toFun (e x)) (basisVec i) ∂volume) =
          -∫ x in U, vecDot (u.grad x) z * φ (e x) ∂volume := hdir'
      _ = J * (-∫ x in e '' U,
          vecDot (u.grad (e.symm x)) z * φ x ∂volume) := by
        rw [hright']
        ring
  exact mul_left_cancel₀ hJ hscaled

/-- Pull an `H¹(U)` representative forward to the linear image `e '' U`.
The value and transformed native gradient are retained definitionally. -/
def compLinearEquiv (e : Vec d ≃L[ℝ] Vec d)
    (u : H1Function U) : H1Function (e '' U) where
  toFun := fun x => u (e.symm x)
  grad := fun x i => vecDot (u.grad (e.symm x)) (e.symm (basisVec i))
  memL2 := memL2On_comp_symm e u.memL2
  gradMemL2 := fun i => gradCoord_comp_symm_memL2 e u i
  hasWeakGradient := hasWeakGradient_compLinearEquiv e u

@[simp]
theorem compLinearEquiv_apply (e : Vec d ≃L[ℝ] Vec d)
    (u : H1Function U) (x : Vec d) :
    u.compLinearEquiv e x = u (e.symm x) :=
  rfl

@[simp]
theorem compLinearEquiv_grad_apply (e : Vec d ≃L[ℝ] Vec d)
    (u : H1Function U) (x : Vec d) (i : Fin d) :
    (u.compLinearEquiv e).grad x i =
      vecDot (u.grad (e.symm x)) (e.symm (basisVec i)) :=
  rfl

end H1Function

end

end PDE
