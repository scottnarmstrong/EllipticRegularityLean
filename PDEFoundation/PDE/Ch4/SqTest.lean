module

public import PDEFoundation.PDE.Ch4.ProductTest

/-!
# Cutoff-squared tests with Lipschitz cutoffs

For a bounded Euclidean-Lipschitz cutoff `η` with compact support in the bounded open set `U`,
the test `η² v` (`v ∈ H¹(U)`, `v ≥ 0`) tests subharmonic / superharmonic functions, with
`∇(η²) = 2 η ∇η` almost everywhere.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- `∇(η²) = 2 η ∇η` at every point of differentiability of a Lipschitz `η`. -/
theorem classicalGradient_sq_ae {L : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      classicalGradient (fun y => η y ^ 2) x = (2 * η x) • classicalGradient η x := by
  filter_upwards [hη.ae_differentiableAt hL] with x hx
  funext i
  simp only [classicalGradient, Pi.smul_apply, smul_eq_mul]
  have hsquare : (fun y => η y ^ 2) = η * η := by
    funext y; simp only [Pi.mul_apply, pow_two]
  rw [hsquare, fderiv_mul hx hx]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem eucLip_sq {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hM : ∀ x, |η x| ≤ M) :
    EucLip (M * L + M * L) (fun y => η y ^ 2) := by
  simpa only [pow_two] using hη.mul hη hM hM

theorem abs_sq_le {M : ℝ} {η : Vec d → ℝ} (hM : ∀ x, |η x| ≤ M) (x : Vec d) :
    |η x ^ 2| ≤ M * M := by
  rw [abs_pow]
  have := hM x
  nlinarith [abs_nonneg (η x)]

theorem hasCompactSupport_sq' {η : Vec d → ℝ} (hηc : HasCompactSupport η) :
    HasCompactSupport (fun y => η y ^ 2) := by
  have hsquare : (fun x => η x ^ 2) = η * η := by
    funext x; simp only [Pi.mul_apply, pow_two]
  rw [hsquare]
  exact hηc.mul_right (f' := η)

theorem tsupport_sq_subset' {η : Vec d → ℝ} (hηU : tsupport η ⊆ U) :
    tsupport (fun y => η y ^ 2) ⊆ U := by
  simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η)).trans hηU

theorem sq_cross_eq_ae {L : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L)
    (v : H1Function U) (F : Vec d → Vec d) :
    (fun x => v.toFun x * vecDot (F x) (classicalGradient (fun y => η y ^ 2) x)) =ᵐ[volumeOn U]
      fun x => 2 * η x * v.toFun x * vecDot (F x) (classicalGradient η x) := by
  filter_upwards [ae_restrict_of_ae (classicalGradient_sq_ae hη hL)] with x hx
  simp only [hx, DGNM.vecDot_smul_right]
  ring

/-- **The `η² v` test, subharmonic.** -/
theorem subharmonic_sqTest_lip (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, 2 * η x * v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) ≤ 0 := by
  obtain ⟨h1, h2, hle⟩ := subharmonic_productTest_lip hU hfin ha hEll hsub v hv
    (eucLip_sq hη hM) (add_nonneg (mul_nonneg ((abs_nonneg _).trans (hM 0)) hL)
      (mul_nonneg ((abs_nonneg _).trans (hM 0)) hL)) (abs_sq_le hM)
    (hasCompactSupport_sq' hηc) (tsupport_sq_subset' hηU) (fun x => sq_nonneg (η x))
  have hcross := sq_cross_eq_ae hη hL v (fun x => matVecMul (a x) (u.grad x))
  refine ⟨h1, h2.congr_fun_ae hcross, ?_⟩
  rw [← integral_congr_ae hcross]
  exact hle

/-- **The `η² v` test, superharmonic.** -/
theorem superharmonic_sqTest_lip (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      0 ≤ (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, 2 * η x * v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) := by
  obtain ⟨h1, h2, hle⟩ := superharmonic_productTest_lip hU hfin ha hEll hsuper v hv
    (eucLip_sq hη hM) (add_nonneg (mul_nonneg ((abs_nonneg _).trans (hM 0)) hL)
      (mul_nonneg ((abs_nonneg _).trans (hM 0)) hL)) (abs_sq_le hM)
    (hasCompactSupport_sq' hηc) (tsupport_sq_subset' hηU) (fun x => sq_nonneg (η x))
  have hcross := sq_cross_eq_ae hη hL v (fun x => matVecMul (a x) (u.grad x))
  refine ⟨h1, h2.congr_fun_ae hcross, ?_⟩
  rw [← integral_congr_ae hcross]
  exact hle

/-- **The `η² v` test, solution.** -/
theorem solution_sqTest_lip (hU : IsOpen U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (v : H1Function U)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, 2 * η x * v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) = 0 := by
  obtain ⟨h1, h2, hle⟩ := solution_productTest_lip hU ha hEll hsol v
    (eucLip_sq hη hM) (add_nonneg (mul_nonneg ((abs_nonneg _).trans (hM 0)) hL)
      (mul_nonneg ((abs_nonneg _).trans (hM 0)) hL)) (abs_sq_le hM)
    (hasCompactSupport_sq' hηc) (tsupport_sq_subset' hηU)
  have hcross := sq_cross_eq_ae hη hL v (fun x => matVecMul (a x) (u.grad x))
  refine ⟨h1, h2.congr_fun_ae hcross, ?_⟩
  rw [← integral_congr_ae hcross]
  exact hle

end PDE.Ch4Infra
