module

public import PDEFoundation.PDE.DGNM.ScalingMeasure
public import PDEFoundation.PDE.DGNM.Restrict
public import PDEFoundation.Sobolev.H1.Affine

/-!
# Translation and dilation to the unit ball

Let `u ∈ H¹(U)` and `euclideanBall x₀ r ⊆ U` with `r > 0`. The blow-up

`ũ(y) = u(r • y + x₀)`, `∇ũ(y) = r • ∇u(r • y + x₀)`

is an `H¹` function on the unit ball `euclideanBall 0 1` (`blowUp`). If `u` is
subharmonic (superharmonic, a homogeneous solution) for `a` on `U`, then `ũ` is
subharmonic (superharmonic, a homogeneous solution) for the blown-up
coefficient field `ã(y) = a(r • y + x₀)` on the unit ball, and `ã` again has
a.e.-measurable entries and is `IsEllipticMatrix 1 Λ` on the unit ball.

Change-of-variables facts for transferring norms back are in
`PDEFoundation.PDE.DGNM.ScalingMeasure`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ}

/-- Replace the domain, value and gradient of an `H1Function` by
propositionally equal data; the new data are kept definitionally. -/
def H1copy {U V : Set (Vec d)} (u : H1Function U) (hUV : U = V)
    (f : Vec d → ℝ) (hf : ∀ x, f x = u.toFun x)
    (g : Vec d → Vec d) (hg : ∀ x, g x = u.grad x) : H1Function V where
  toFun := f
  grad := g
  memL2 := by
    subst hUV
    rw [show f = u.toFun from funext hf]
    exact u.memL2
  gradMemL2 := by
    subst hUV
    rw [show g = u.grad from funext hg]
    exact u.gradMemL2
  hasWeakGradient := by
    subst hUV
    rw [show f = u.toFun from funext hf, show g = u.grad from funext hg]
    exact u.hasWeakGradient

theorem unitBall_subset_dilate {U : Set (Vec d)} (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) :
    euclideanBall (0 : Vec d) 1 ⊆ r⁻¹ • translateSet (-x₀) U := by
  intro y hy
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne'),
    mem_translateSet_iff_sub_mem, inv_inv, sub_neg_eq_add]
  apply hball
  have := (affineScale_mem_euclideanBall_iff x₀ hr 1 y).mpr hy
  rwa [mul_one] at this

/-- The blow-up `ũ(y) = u(r • y + x₀)` on the unit ball. -/
noncomputable def blowUp {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) :
    H1Function (euclideanBall (0 : Vec d) 1) :=
  H1copy (r • (((u.translate (-x₀)).dilate (inv_pos.mpr hr)).restrict
      (isOpen_euclideanBall 0 1) (unitBall_subset_dilate x₀ hr hball))) rfl
    (fun y => u (r • y + x₀))
    (fun y => by
      simp only [H1Function.smul_toFun, H1Function.restrict_toFun,
        H1Function.dilate_toFun, H1Function.translate_toFun, inv_inv,
        sub_neg_eq_add]
      field_simp)
    (fun y => r • u.grad (r • y + x₀))
    (fun y => by
      simp only [H1Function.smul_grad, H1Function.restrict_grad,
        H1Function.dilate_grad, H1Function.translate_grad, inv_inv,
        sub_neg_eq_add])

@[simp]
theorem blowUp_toFun {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) (y : Vec d) :
    (blowUp u x₀ hr hball).toFun y = u (r • y + x₀) :=
  rfl

@[simp]
theorem blowUp_grad {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) (y : Vec d) :
    (blowUp u x₀ hr hball).grad y = r • u.grad (r • y + x₀) :=
  rfl

/-- A.e. pointwise information on `u` transfers to the blow-up. -/
theorem ae_blowUp_of_ae {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) {P : ℝ → Prop}
    (h : ∀ᵐ x ∂volumeOn U, P (u x)) :
    ∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) 1), P ((blowUp u x₀ hr hball) y) := by
  have h' : ∀ᵐ x ∂volumeOn (euclideanBall x₀ (r * 1)), P (u x) := by
    rw [mul_one]
    exact ae_restrict_of_ae_restrict_of_subset hball h
  exact (ae_comp_affineScale_ball_iff x₀ hr 1).mpr h'

/-- The blown-up coefficient field `ã(y) = a(r • y + x₀)`. -/
def blowUpCoeff (a : CoeffField d) (x₀ : Vec d) (r : ℝ) : CoeffField d :=
  fun y => a (r • y + x₀)

@[simp]
theorem blowUpCoeff_apply (a : CoeffField d) (x₀ : Vec d) (r : ℝ) (y : Vec d) :
    blowUpCoeff a x₀ r y = a (r • y + x₀) :=
  rfl

/-- The blown-up coefficient field is elliptic on the unit ball. -/
theorem blowUpCoeff_elliptic {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hball : euclideanBall x₀ r ⊆ U) :
    ∀ y ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (blowUpCoeff a x₀ r y) := by
  intro y hy
  apply hEll
  apply hball
  have := (affineScale_mem_euclideanBall_iff x₀ hr 1 y).mpr hy
  rwa [mul_one] at this

/-- The blown-up coefficient field has a.e.-measurable entries on the unit
ball. -/
theorem blowUpCoeff_aemeasurable {U : Set (Vec d)} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U)) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) :
    ∀ i j, AEMeasurable (fun y => blowUpCoeff a x₀ r y i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  intro i j
  have hset : translateSet x₀ (r • euclideanBall (0 : Vec d) 1) = euclideanBall x₀ r := by
    rw [translateSet_smul_euclideanBall x₀ hr 1, mul_one]
  have hB : AEMeasurable (fun x => a x i j)
      (volumeOn (translateSet x₀ (r • euclideanBall (0 : Vec d) 1))) := by
    rw [hset]
    exact (ha i j).mono_measure (Measure.restrict_mono hball le_rfl)
  exact aemeasurable_comp_affineScale x₀ hr hB

/-! ### Pulled-back tests -/

/-- A smooth test on the unit ball, pulled back to `euclideanBall x₀ r`:
`ψ(x) = φ(r⁻¹ • (x - x₀))`. -/
noncomputable def pullTest (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (euclideanBall (0 : Vec d) 1)) :
    WeakTestFunction (euclideanBall x₀ r) where
  toFun := fun x => φ (r⁻¹ • (x - x₀))
  contDiff := φ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  hasCompactSupport := by
    have hfun : (fun x => φ (r⁻¹ • (x - x₀))) =
        φ.toFun ∘ (affineScale x₀ hr.ne').symm := by
      funext x
      simp only [Function.comp_apply]
      congr 1
    rw [hfun]
    exact φ.hasCompactSupport.comp_homeomorph _
  tsupport_subset := by
    have hfun : (fun x => φ (r⁻¹ • (x - x₀))) =
        φ.toFun ∘ (affineScale x₀ hr.ne').symm := by
      funext x
      simp only [Function.comp_apply]
      congr 1
    intro x hx
    rw [hfun, tsupport_comp_eq_preimage] at hx
    have hy := φ.tsupport_subset hx
    have hmem := (affineScale_mem_euclideanBall_iff x₀ hr 1 _).mpr hy
    rw [mul_one] at hmem
    have hx' : r • ((affineScale x₀ hr.ne').symm x) + x₀ = x := by
      rw [← affineScale_apply x₀ hr.ne', Homeomorph.apply_symm_apply]
    rwa [hx'] at hmem

theorem pullTest_apply (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (euclideanBall (0 : Vec d) 1)) (x : Vec d) :
    pullTest x₀ hr φ x = φ (r⁻¹ • (x - x₀)) :=
  rfl

theorem pullTest_grad (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (euclideanBall (0 : Vec d) 1)) (x : Vec d) :
    (pullTest x₀ hr φ).grad x = r⁻¹ • φ.grad (r⁻¹ • (x - x₀)) := by
  have hA : HasFDerivAt (fun x : Vec d => r⁻¹ • (x - x₀))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
    ((hasFDerivAt_id x).sub_const x₀).const_smul r⁻¹
  have hφd : HasFDerivAt φ.toFun (fderiv ℝ φ.toFun (r⁻¹ • (x - x₀)))
      (r⁻¹ • (x - x₀)) :=
    ((φ.contDiff.differentiable (by simp)) _).hasFDerivAt
  have hcomp := (hφd.comp x hA).fderiv
  funext i
  simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv,
    Pi.smul_apply, smul_eq_mul]
  change fderiv ℝ (φ.toFun ∘ fun x : Vec d => r⁻¹ • (x - x₀)) x (basisVec i) = _
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem pullTest_nonnegative (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {φ : WeakTestFunction (euclideanBall (0 : Vec d) 1)} (hφ : φ.Nonnegative) :
    (pullTest x₀ hr φ).Nonnegative :=
  fun _ => hφ _

/-! ### The flux identity -/

variable {U : Set (Vec d)} {a : CoeffField d}

/-- The tested flux of the blow-up is `r² (r^d)⁻¹` times the tested flux of
`u` against the pulled-back test (with integrability transferred). -/
theorem blowUp_flux (hUOpen : IsOpen U) (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U)
    (φ : WeakTestFunction (euclideanBall (0 : Vec d) 1))
    (hint : IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
      ((extendTest hball (pullTest x₀ hr φ)).grad x)) U) :
    IntegrableOn (fun y => vecDot (matVecMul (blowUpCoeff a x₀ r y)
        ((blowUp u x₀ hr hball).grad y)) (φ.grad y)) (euclideanBall (0 : Vec d) 1) ∧
      ∫ y in euclideanBall (0 : Vec d) 1, vecDot (matVecMul (blowUpCoeff a x₀ r y)
          ((blowUp u x₀ hr hball).grad y)) (φ.grad y) =
        r ^ 2 * (r ^ d)⁻¹ * ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          ((extendTest hball (pullTest x₀ hr φ)).grad x) := by
  set F : Vec d → ℝ := fun x => vecDot (matVecMul (a x) (u.grad x))
    ((pullTest x₀ hr φ).grad x) with hFdef
  have hset : translateSet x₀ (r • euclideanBall (0 : Vec d) 1) = euclideanBall x₀ r := by
    rw [translateSet_smul_euclideanBall x₀ hr 1, mul_one]
  have hpoint : ∀ y, vecDot (matVecMul (blowUpCoeff a x₀ r y)
      ((blowUp u x₀ hr hball).grad y)) (φ.grad y) = r ^ 2 * F (r • y + x₀) := by
    intro y
    have hy : r⁻¹ • (r • y + x₀ - x₀) = y := by
      rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    simp only [hFdef, blowUpCoeff_apply, blowUp_grad, pullTest_grad, hy,
      matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    field_simp
  rw [extendTest_grad] at hint ⊢
  have hFint : IntegrableOn F (euclideanBall x₀ r) := hint.mono_set hball
  rw [← hset] at hFint
  have hcomp := integrableOn_comp_affineScale x₀ hr hFint
  refine ⟨?_, ?_⟩
  · simp_rw [hpoint]
    exact hcomp.const_mul _
  · simp_rw [hpoint]
    rw [integral_const_mul, setIntegral_comp_affineScale x₀ hr, hset,
      setIntegral_vecDot_extendTest hUOpen.measurableSet hball]
    ring

/-! ### Class transport -/

/-- **Blow-up of a subharmonic function.** If `u` is subharmonic for `a` on
the open set `U ⊇ euclideanBall x₀ r`, then `ũ(y) = u(r • y + x₀)` is
subharmonic for `ã(y) = a(r • y + x₀)` on the unit ball. -/
theorem subharmonicOn_blowUp (hUOpen : IsOpen U) {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) :
    IsWeakDivergenceFormSubharmonicOn (blowUpCoeff a x₀ r)
      (euclideanBall (0 : Vec d) 1) (blowUp u x₀ hr hball) := by
  rw [subharmonicOn_iff] at hsub ⊢
  intro φ hφ
  obtain ⟨hi, hle⟩ := hsub (extendTest hball (pullTest x₀ hr φ))
    (extendTest_nonnegative hball (pullTest_nonnegative x₀ hr hφ))
  obtain ⟨hi', heq⟩ := blowUp_flux hUOpen u x₀ hr hball φ hi
  refine ⟨hi', ?_⟩
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hle

/-- **Blow-up of a superharmonic function.** -/
theorem superharmonicOn_blowUp (hUOpen : IsOpen U) {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) :
    IsWeakDivergenceFormSuperharmonicOn (blowUpCoeff a x₀ r)
      (euclideanBall (0 : Vec d) 1) (blowUp u x₀ hr hball) := by
  rw [superharmonicOn_iff] at hsuper ⊢
  intro φ hφ
  obtain ⟨hi, hle⟩ := hsuper (extendTest hball (pullTest x₀ hr φ))
    (extendTest_nonnegative hball (pullTest_nonnegative x₀ hr hφ))
  obtain ⟨hi', heq⟩ := blowUp_flux hUOpen u x₀ hr hball φ hi
  refine ⟨hi', ?_⟩
  rw [heq]
  exact mul_nonneg (by positivity) hle

/-- **Blow-up of a homogeneous solution.** -/
theorem solutionOn_blowUp (hUOpen : IsOpen U) {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) (x₀ : Vec d)
    {r : ℝ} (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ U) :
    IsWeakDivergenceFormSolutionOn (blowUpCoeff a x₀ r)
      (euclideanBall (0 : Vec d) 1) (blowUp u x₀ hr hball) (0 : Vec d → ℝ) 0 := by
  rw [solutionOn_iff] at hsol ⊢
  intro φ
  obtain ⟨hi, heq0⟩ := hsol (extendTest hball (pullTest x₀ hr φ))
  obtain ⟨hi', heq⟩ := blowUp_flux hUOpen u x₀ hr hball φ hi
  refine ⟨hi', ?_⟩
  rw [heq, heq0, mul_zero]

end DGNM

end PDE
