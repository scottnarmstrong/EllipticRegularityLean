module

public import PDEFoundation.PDE.DGNM.ClassAlgebra

/-!
# Restriction of homogeneous sub/super/solutions to open subdomains

The restricted `H1Function` (`H1Function.restrict`) keeps the literal value and
gradient representatives. A smooth test supported in the smaller domain is a
smooth test in the larger domain, and its gradient vanishes off the smaller
domain.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U V : Set (Vec d)} {a : CoeffField d}

/-- A smooth test on `V ⊆ U`, regarded as a test on `U`. -/
def extendTest (hVU : V ⊆ U) (φ : WeakTestFunction V) : WeakTestFunction U where
  toFun := φ.toFun
  contDiff := φ.contDiff
  hasCompactSupport := φ.hasCompactSupport
  tsupport_subset := φ.tsupport_subset.trans hVU

@[simp]
theorem extendTest_apply (hVU : V ⊆ U) (φ : WeakTestFunction V) (x : Vec d) :
    extendTest hVU φ x = φ x :=
  rfl

@[simp]
theorem extendTest_grad (hVU : V ⊆ U) (φ : WeakTestFunction V) :
    (extendTest hVU φ).grad = φ.grad :=
  rfl

theorem extendTest_nonnegative (hVU : V ⊆ U) {φ : WeakTestFunction V}
    (hφ : φ.Nonnegative) : (extendTest hVU φ).Nonnegative :=
  hφ

/-- The gradient of a test supported in `V` vanishes outside `V`. -/
theorem WeakTestFunction.grad_eq_zero_of_notMem (φ : WeakTestFunction V)
    {x : Vec d} (hx : x ∉ V) : φ.grad x = 0 := by
  have hxt : x ∉ tsupport φ.toFun := fun hmem => hx (φ.tsupport_subset hmem)
  funext i
  simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv]
  rw [fderiv_of_notMem_tsupport ℝ hxt]
  simp

/-- The tested flux over `U` of a test supported in `V ⊆ U` equals the tested
flux over `V`. -/
theorem setIntegral_vecDot_extendTest (hU : MeasurableSet U) (hVU : V ⊆ U)
    (F : Vec d → Vec d) (φ : WeakTestFunction V) :
    ∫ x in U, vecDot (F x) (φ.grad x) = ∫ x in V, vecDot (F x) (φ.grad x) :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hVU fun x hx => by
    rw [WeakTestFunction.grad_eq_zero_of_notMem φ hx.2, vecDot_zero_right]

/-- Restriction of a subharmonic function to an open subdomain. -/
theorem subharmonicOn_restrict {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    IsWeakDivergenceFormSubharmonicOn a V (u.restrict hVOpen hVU) := by
  rw [subharmonicOn_iff] at hsub ⊢
  intro φ hφ
  rcases hsub (extendTest hVU φ) (extendTest_nonnegative hVU hφ) with ⟨hi, hle⟩
  rw [extendTest_grad] at hi hle
  rw [setIntegral_vecDot_extendTest hUOpen.measurableSet hVU] at hle
  exact ⟨by simpa only [H1Function.restrict_grad] using hi.mono_set hVU,
    by simpa only [H1Function.restrict_grad] using hle⟩

/-- Restriction of a superharmonic function to an open subdomain. -/
theorem superharmonicOn_restrict {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    IsWeakDivergenceFormSuperharmonicOn a V (u.restrict hVOpen hVU) := by
  rw [superharmonicOn_iff] at hsuper ⊢
  intro φ hφ
  rcases hsuper (extendTest hVU φ) (extendTest_nonnegative hVU hφ) with
    ⟨hi, hle⟩
  rw [extendTest_grad] at hi hle
  rw [setIntegral_vecDot_extendTest hUOpen.measurableSet hVU] at hle
  exact ⟨by simpa only [H1Function.restrict_grad] using hi.mono_set hVU,
    by simpa only [H1Function.restrict_grad] using hle⟩

/-- Restriction of a homogeneous solution to an open subdomain. -/
theorem solutionOn_restrict {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (hUOpen : IsOpen U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    IsWeakDivergenceFormSolutionOn a V (u.restrict hVOpen hVU)
      (0 : Vec d → ℝ) 0 :=
  IsWeakDivergenceFormSolutionOn.restrict hsol hUOpen hVOpen hVU

/-- The coefficient hypotheses restrict to subdomains. -/
theorem aemeasurable_coeff_mono (hVU : V ⊆ U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U)) :
    ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn V) :=
  fun i j => (ha i j).mono_measure (Measure.restrict_mono hVU le_rfl)

end DGNM

end PDE
