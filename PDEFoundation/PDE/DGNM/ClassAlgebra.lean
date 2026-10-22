module

public import PDEFoundation.PDE.DGNM.Bridge
public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.H1.Mean

/-!
# Algebraic stability of the homogeneous sub/super/solution classes

For the homogeneous smooth-test predicates we record

* the clean characterizations `subharmonicOn_iff`, `superharmonicOn_iff`,
  `solutionOn_iff` (the zero source and forcing terms are discharged once);
* negation (`u` superharmonic iff `-u` subharmonic);
* nonnegative scalar multiples, and arbitrary multiples of solutions;
* adding or subtracting a constant;
* restriction to an open subdomain.

No measurability or ellipticity hypothesis is needed for any of these.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

private theorem zero_rhs (φ : WeakTestFunction U) :
    (∫ x in U, (0 : Vec d → ℝ) x * φ x) -
        ∫ x in U, vecDot ((0 : Vec d → Vec d) x) (φ.grad x) = 0 := by
  simp only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
    integral_zero, sub_zero]

private theorem zero_testable {u : H1Function U} (φ : WeakTestFunction U)
    (hflux : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U) :
    WeakDivergenceFormTestableOn a U u 0 0 φ := by
  refine ⟨hflux, ?_, ?_⟩
  · simp only [Pi.zero_apply, zero_mul]
    exact integrableOn_zero
  · simp only [Pi.zero_apply, vecDot, zero_mul, Finset.sum_const_zero]
    exact integrableOn_zero

/-- Clean characterization of the homogeneous smooth-test subharmonic
predicate. -/
theorem subharmonicOn_iff {u : H1Function U} :
    IsWeakDivergenceFormSubharmonicOn a U u ↔
      ∀ φ : WeakTestFunction U, φ.Nonnegative →
        IntegrableOn
            (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U ∧
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) ≤ 0 := by
  constructor
  · intro h φ hφ
    rcases h φ hφ with ⟨ht, hineq⟩
    rw [zero_rhs] at hineq
    exact ⟨ht.flux_integrable, hineq⟩
  · intro h φ hφ
    rcases h φ hφ with ⟨hi, hle⟩
    refine ⟨zero_testable φ hi, ?_⟩
    rw [zero_rhs]
    exact hle

/-- Clean characterization of the homogeneous smooth-test superharmonic
predicate. -/
theorem superharmonicOn_iff {u : H1Function U} :
    IsWeakDivergenceFormSuperharmonicOn a U u ↔
      ∀ φ : WeakTestFunction U, φ.Nonnegative →
        IntegrableOn
            (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U ∧
          0 ≤ ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) := by
  constructor
  · intro h φ hφ
    rcases h φ hφ with ⟨ht, hineq⟩
    rw [zero_rhs] at hineq
    exact ⟨ht.flux_integrable, hineq⟩
  · intro h φ hφ
    rcases h φ hφ with ⟨hi, hle⟩
    refine ⟨zero_testable φ hi, ?_⟩
    rw [zero_rhs]
    exact hle

/-- Clean characterization of the homogeneous smooth-test solution
predicate. -/
theorem solutionOn_iff {u : H1Function U} :
    IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0 ↔
      ∀ φ : WeakTestFunction U,
        IntegrableOn
            (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) U ∧
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) = 0 := by
  constructor
  · intro h φ
    rcases h φ with ⟨ht, hid⟩
    rw [zero_rhs] at hid
    exact ⟨ht.flux_integrable, hid⟩
  · intro h φ
    rcases h φ with ⟨hi, hid⟩
    refine ⟨zero_testable φ hi, ?_⟩
    rw [zero_rhs]
    exact hid

/-- A homogeneous solution is subharmonic. -/
theorem subharmonicOn_of_solutionOn {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSubharmonicOn a U u :=
  IsWeakDivergenceFormSolutionOn.toSubsolutionOn hsol

/-- A homogeneous solution is superharmonic. -/
theorem superharmonicOn_of_solutionOn {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSuperharmonicOn a U u :=
  IsWeakDivergenceFormSolutionOn.toSupersolutionOn hsol

/-! ### Scalar multiples -/

private theorem flux_smul (c : ℝ) (u : H1Function U) (φ : WeakTestFunction U) :
    (fun x => vecDot (matVecMul (a x) ((c • u).grad x)) (φ.grad x)) =
      fun x => c * vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) := by
  funext x
  rw [H1Function.smul_grad, matVecMul_smul, vecDot_smul_left]

/-- A nonnegative multiple of a subharmonic function is subharmonic. -/
theorem subharmonicOn_smul {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) {c : ℝ} (hc : 0 ≤ c) :
    IsWeakDivergenceFormSubharmonicOn a U (c • u) := by
  rw [subharmonicOn_iff] at hsub ⊢
  intro φ hφ
  rcases hsub φ hφ with ⟨hi, hle⟩
  rw [flux_smul, integral_const_mul]
  exact ⟨hi.const_mul c, mul_nonpos_of_nonneg_of_nonpos hc hle⟩

/-- A nonnegative multiple of a superharmonic function is superharmonic. -/
theorem superharmonicOn_smul {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) {c : ℝ} (hc : 0 ≤ c) :
    IsWeakDivergenceFormSuperharmonicOn a U (c • u) := by
  rw [superharmonicOn_iff] at hsuper ⊢
  intro φ hφ
  rcases hsuper φ hφ with ⟨hi, hle⟩
  rw [flux_smul, integral_const_mul]
  exact ⟨hi.const_mul c, mul_nonneg hc hle⟩

/-- A nonpositive multiple of a superharmonic function is subharmonic. -/
theorem subharmonicOn_smul_of_nonpos {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) {c : ℝ} (hc : c ≤ 0) :
    IsWeakDivergenceFormSubharmonicOn a U (c • u) := by
  rw [superharmonicOn_iff] at hsuper
  rw [subharmonicOn_iff]
  intro φ hφ
  rcases hsuper φ hφ with ⟨hi, hle⟩
  rw [flux_smul, integral_const_mul]
  exact ⟨hi.const_mul c, mul_nonpos_of_nonpos_of_nonneg hc hle⟩

/-- A nonpositive multiple of a subharmonic function is superharmonic. -/
theorem superharmonicOn_smul_of_nonpos {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) {c : ℝ} (hc : c ≤ 0) :
    IsWeakDivergenceFormSuperharmonicOn a U (c • u) := by
  rw [subharmonicOn_iff] at hsub
  rw [superharmonicOn_iff]
  intro φ hφ
  rcases hsub φ hφ with ⟨hi, hle⟩
  rw [flux_smul, integral_const_mul]
  exact ⟨hi.const_mul c, mul_nonneg_of_nonpos_of_nonpos hc hle⟩

/-- Every multiple of a homogeneous solution is a homogeneous solution. -/
theorem solutionOn_smul {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) (c : ℝ) :
    IsWeakDivergenceFormSolutionOn a U (c • u) (0 : Vec d → ℝ) 0 := by
  rw [solutionOn_iff] at hsol ⊢
  intro φ
  rcases hsol φ with ⟨hi, hid⟩
  rw [flux_smul, integral_const_mul, hid, mul_zero]
  exact ⟨hi.const_mul c, rfl⟩

/-! ### Negation -/

private theorem flux_neg (u : H1Function U) (φ : WeakTestFunction U) :
    (fun x => vecDot (matVecMul (a x) ((-u).grad x)) (φ.grad x)) =
      fun x => -vecDot (matVecMul (a x) (u.grad x)) (φ.grad x) := by
  funext x
  rw [H1Function.neg_grad, matVecMul_neg, vecDot_neg_left]

/-- The negative of a superharmonic function is subharmonic. -/
theorem subharmonicOn_neg {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) :
    IsWeakDivergenceFormSubharmonicOn a U (-u) := by
  rw [superharmonicOn_iff] at hsuper
  rw [subharmonicOn_iff]
  intro φ hφ
  rcases hsuper φ hφ with ⟨hi, hle⟩
  rw [flux_neg, integral_neg]
  exact ⟨hi.neg, neg_nonpos.mpr hle⟩

/-- The negative of a subharmonic function is superharmonic. -/
theorem superharmonicOn_neg {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) :
    IsWeakDivergenceFormSuperharmonicOn a U (-u) := by
  rw [subharmonicOn_iff] at hsub
  rw [superharmonicOn_iff]
  intro φ hφ
  rcases hsub φ hφ with ⟨hi, hle⟩
  rw [flux_neg, integral_neg]
  exact ⟨hi.neg, neg_nonneg.mpr hle⟩

/-- `-u` is subharmonic iff `u` is superharmonic. -/
theorem subharmonicOn_neg_iff {u : H1Function U} :
    IsWeakDivergenceFormSubharmonicOn a U (-u) ↔
      IsWeakDivergenceFormSuperharmonicOn a U u := by
  refine ⟨fun h => ?_, subharmonicOn_neg⟩
  simpa only [neg_neg] using superharmonicOn_neg h

/-- `-u` is superharmonic iff `u` is subharmonic. -/
theorem superharmonicOn_neg_iff {u : H1Function U} :
    IsWeakDivergenceFormSuperharmonicOn a U (-u) ↔
      IsWeakDivergenceFormSubharmonicOn a U u := by
  refine ⟨fun h => ?_, superharmonicOn_neg⟩
  simpa only [neg_neg] using subharmonicOn_neg h

/-- The negative of a homogeneous solution is a homogeneous solution. -/
theorem solutionOn_neg {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormSolutionOn a U (-u) (0 : Vec d → ℝ) 0 := by
  rw [solutionOn_iff] at hsol ⊢
  intro φ
  rcases hsol φ with ⟨hi, hid⟩
  rw [flux_neg, integral_neg, hid, neg_zero]
  exact ⟨hi.neg, rfl⟩

/-! ### Adding constants -/

section Constants

variable [IsFiniteMeasure (volumeOn U)]

/-- Adding a constant preserves subharmonicity. -/
theorem subharmonicOn_addConst {u : H1Function U}
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U (u.addConst c) := by
  rw [subharmonicOn_iff] at hsub ⊢
  intro φ hφ
  simpa only [H1Function.grad_addConst] using hsub φ hφ

/-- Adding a constant preserves superharmonicity. -/
theorem superharmonicOn_addConst {u : H1Function U}
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSuperharmonicOn a U (u.addConst c) := by
  rw [superharmonicOn_iff] at hsuper ⊢
  intro φ hφ
  simpa only [H1Function.grad_addConst] using hsuper φ hφ

/-- Adding a constant preserves homogeneous solutions. -/
theorem solutionOn_addConst {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) (c : ℝ) :
    IsWeakDivergenceFormSolutionOn a U (u.addConst c) (0 : Vec d → ℝ) 0 := by
  rw [solutionOn_iff] at hsol ⊢
  intro φ
  simpa only [H1Function.grad_addConst] using hsol φ

end Constants

/-- Subtracting a constant preserves subharmonicity. -/
theorem subharmonicOn_subConst {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hsub : IsWeakDivergenceFormSubharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U (u.subConst hU c) := by
  rw [subharmonicOn_iff] at hsub ⊢
  intro φ hφ
  simpa only [H1Function.grad_subConst] using hsub φ hφ

/-- Subtracting a constant preserves superharmonicity. -/
theorem superharmonicOn_subConst {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSuperharmonicOn a U (u.subConst hU c) := by
  rw [superharmonicOn_iff] at hsuper ⊢
  intro φ hφ
  simpa only [H1Function.grad_subConst] using hsuper φ hφ

/-- Subtracting a constant preserves homogeneous solutions. -/
theorem solutionOn_subConst {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) (c : ℝ) :
    IsWeakDivergenceFormSolutionOn a U (u.subConst hU c) (0 : Vec d → ℝ) 0 := by
  rw [solutionOn_iff] at hsol ⊢
  intro φ
  simpa only [H1Function.grad_subConst] using hsol φ

end DGNM

end PDE
