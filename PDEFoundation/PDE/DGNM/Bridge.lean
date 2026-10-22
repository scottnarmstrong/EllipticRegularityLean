module

public import PDEFoundation.PDE.CoefficientModification
public import PDEFoundation.PDE.WeakInequalities

/-!
# Class bridges for the De Giorgi-Nash-Moser toolbox

The De Giorgi-Nash-Moser statements use the smooth-test predicates
`IsWeakDivergenceFormSubharmonicOn`, `IsWeakDivergenceFormSuperharmonicOn` and
`IsWeakDivergenceFormSolutionOn` for a coefficient field whose entries are only
almost-everywhere measurable and which is pointwise elliptic on the domain.

This file proves the clean corollaries used by every later argument: under
these hypotheses on a bounded open convex domain, the flux `a ∇u` is in `L²`
and the inequalities (resp. the identity) hold for every nonnegative
(resp. every) representative-level `H¹₀` test, with the integrability of the
tested flux recorded explicitly.

The passage goes through the measurable modification
`exists_isEllipticFieldOn_coeffAEEqOn` and back.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ}

/-! ### Small vector algebra -/

theorem vecDot_add_right (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem vecDot_add_left (x y z : Vec d) :
    vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem vecDot_smul_right (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_smul_left (x y : Vec d) (c : ℝ) :
    vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_neg_left (x y : Vec d) :
    vecDot (-x) y = -vecDot x y := by
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem vecDot_zero_left (y : Vec d) : vecDot (0 : Vec d) y = 0 := by
  simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem vecDot_zero_right (x : Vec d) : vecDot x (0 : Vec d) = 0 := by
  simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem matVecMul_smul (A : Mat d) (c : ℝ) (x : Vec d) :
    matVecMul A (c • x) = c • matVecMul A x := by
  funext i
  simp only [matVecMul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matVecMul_neg (A : Mat d) (x : Vec d) :
    matVecMul A (-x) = -matVecMul A x := by
  funext i
  simp only [matVecMul_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem matVecMul_zero' (A : Mat d) : matVecMul A (0 : Vec d) = 0 := by
  funext i
  simp only [matVecMul_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem matVecMul_indicator {s : Set (Vec d)} (A : Mat d) (G : Vec d → Vec d)
    (x : Vec d) :
    matVecMul A (s.indicator G x) = s.indicator (fun y => matVecMul A (G y)) x := by
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, matVecMul_zero']

/-- The energy density of a uniformly elliptic matrix dominates the Euclidean
square (lower ellipticity constant one). -/
theorem vecNormSq_le_vecDot_matVecMul {Λ : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (ξ : Vec d) :
    vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ) := by
  simpa only [one_mul] using hA.coercive ξ

/-- The energy density is nonnegative. -/
theorem vecDot_matVecMul_self_nonneg {Λ : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (ξ : Vec d) :
    0 ≤ vecDot ξ (matVecMul A ξ) :=
  (vecNormSq_nonneg ξ).trans (vecNormSq_le_vecDot_matVecMul hA ξ)

/-! ### Coefficient bridges -/

variable {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- For an entrywise a.e.-measurable coefficient field which is pointwise
elliptic on `U`, the product with an `L²` vector field is in `L²(U)`. -/
theorem memVectorL2On_matVecMul_of_aemeasurable
    (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {F : Vec d → Vec d} (hF : MemVectorL2On U F) :
    MemVectorL2On U (fun x => matVecMul (a x) (F x)) := by
  obtain ⟨b, hb, hab⟩ := exists_isEllipticFieldOn_coeffAEEqOn hU ha hEll
  have hbF := memVectorL2On_matVecMul_of_isEllipticFieldOn hb hF
  intro i
  refine (hbF i).ae_eq ?_
  filter_upwards [hab] with x hx
  rw [hx]

/-- A smooth-test subharmonic function with a.e.-measurable elliptic
coefficients is subharmonic against every nonnegative `H¹₀` test. -/
theorem h10SubharmonicOn_of_subharmonicOn
    (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u) :
    IsWeakDivergenceFormH10SubharmonicOn a U u := by
  obtain ⟨b, hb, hab⟩ :=
    exists_isEllipticFieldOn_coeffAEEqOn hU.measurableSet ha hEll
  have hsubB := IsWeakDivergenceFormSubsolutionOn.of_ae_eq_coeff hab hsub
  have hH10B :=
    IsWeakDivergenceFormSubsolutionOn.toH10SubharmonicOn hsubB hU hb
  exact IsWeakDivergenceFormH10SubsolutionOn.of_ae_eq_coeff hab.symm hH10B

/-- A smooth-test superharmonic function with a.e.-measurable elliptic
coefficients is superharmonic against every nonnegative `H¹₀` test. -/
theorem h10SuperharmonicOn_of_superharmonicOn
    (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u) :
    IsWeakDivergenceFormH10SuperharmonicOn a U u := by
  obtain ⟨b, hb, hab⟩ :=
    exists_isEllipticFieldOn_coeffAEEqOn hU.measurableSet ha hEll
  have hsuperB := IsWeakDivergenceFormSupersolutionOn.of_ae_eq_coeff hab hsuper
  have hH10B :=
    IsWeakDivergenceFormSupersolutionOn.toH10SuperharmonicOn hsuperB hU hb
  exact IsWeakDivergenceFormH10SupersolutionOn.of_ae_eq_coeff hab.symm hH10B

/-- A smooth-test homogeneous weak solution with a.e.-measurable elliptic
coefficients may be tested against every `H¹₀` function. -/
theorem h10SolutionOn_of_solutionOn
    (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0) :
    IsWeakDivergenceFormH10SolutionOn a U u (0 : Vec d → ℝ) 0 := by
  obtain ⟨b, hb, hab⟩ :=
    exists_isEllipticFieldOn_coeffAEEqOn hU.measurableSet ha hEll
  have hsolB := IsWeakDivergenceFormSolutionOn.of_ae_eq_coeff hab hsol
  have hH10B := IsWeakDivergenceFormHarmonicOn.toH10SolutionOn hsolB hb
  intro φ
  rcases hH10B φ with ⟨htestable, hidentity⟩
  have hfluxAE :
      (fun x => vecDot (matVecMul (b x) (u.grad x))
        (φ.toH1Function.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x) := by
    filter_upwards [hab] with x hx
    rw [hx]
  refine ⟨⟨(integrableOn_congr_fun_ae hfluxAE).mp htestable.flux_integrable,
    htestable.source_integrable, htestable.forcing_integrable⟩, ?_⟩
  rw [← integral_congr_ae hfluxAE]
  exact hidentity

/-! ### Consumer forms of the tested inequalities -/

/-- The all-`H¹₀` subharmonic inequality in consumer form: the tested flux is
integrable and its integral is nonpositive. -/
theorem H10Subharmonic.test {u : H1Function U}
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (φ : H10Function U) (hφ : φ.AENonnegative) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) ≤ 0 := by
  rcases hsub φ hφ with ⟨htestable, hineq⟩
  refine ⟨htestable.flux_integrable, ?_⟩
  simpa only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
    integral_zero, sub_zero] using hineq

/-- The all-`H¹₀` superharmonic inequality in consumer form. -/
theorem H10Superharmonic.test {u : H1Function U}
    (hsuper : IsWeakDivergenceFormH10SuperharmonicOn a U u)
    (φ : H10Function U) (hφ : φ.AENonnegative) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U ∧
      0 ≤ ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) := by
  rcases hsuper φ hφ with ⟨htestable, hineq⟩
  refine ⟨htestable.flux_integrable, ?_⟩
  simpa only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
    integral_zero, sub_zero] using hineq

/-- The all-`H¹₀` homogeneous identity in consumer form. -/
theorem H10Solution.test {u : H1Function U}
    (hsol : IsWeakDivergenceFormH10SolutionOn a U u (0 : Vec d → ℝ) 0)
    (φ : H10Function U) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) = 0 := by
  rcases hsol φ with ⟨htestable, hid⟩
  refine ⟨htestable.flux_integrable, ?_⟩
  simpa only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
    integral_zero, sub_zero] using hid

/-- **Class bridge (subharmonic).** Under the hypotheses, a smooth-test
subharmonic function satisfies `∫ a∇u·∇φ ≤ 0`, with integrable integrand, for
every a.e.-nonnegative `H¹₀` test `φ`. -/
theorem subharmonic_test
    (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (φ : H10Function U) (hφ : φ.AENonnegative) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) ≤ 0 :=
  H10Subharmonic.test (h10SubharmonicOn_of_subharmonicOn hU ha hEll hsub) φ hφ

/-- **Class bridge (superharmonic).** Under the hypotheses, a
smooth-test superharmonic function satisfies `0 ≤ ∫ a∇u·∇φ`, with integrable
integrand, for every a.e.-nonnegative `H¹₀` test `φ`. -/
theorem superharmonic_test
    (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (φ : H10Function U) (hφ : φ.AENonnegative) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U ∧
      0 ≤ ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) :=
  H10Superharmonic.test
    (h10SuperharmonicOn_of_superharmonicOn hU ha hEll hsuper) φ hφ

/-- **Class bridge (solution).** Under the hypotheses, a smooth-test
homogeneous weak solution satisfies `∫ a∇u·∇φ = 0`, with integrable
integrand, for every `H¹₀` test `φ`. -/
theorem solution_test
    (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (φ : H10Function U) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x)) U ∧
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) = 0 :=
  H10Solution.test (h10SolutionOn_of_solutionOn hU ha hEll hsol) φ

end DGNM

end PDE
