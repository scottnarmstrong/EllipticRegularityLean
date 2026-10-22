module

public import PDEFoundation.PDE.DGNM.Bridge
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# Product tests `ψ v` and `η² v`

For an `H¹(U)` function `v` and a globally smooth compactly supported
multiplier `ψ` with `tsupport ψ ⊆ U`, the product `ψ v` is a concrete
`H¹₀(U)` test (`H1Function.mulContDiffHasCompactSupportToH10`) with gradient
`ψ ∇v + v ∇ψ`. Testing a subharmonic (resp. superharmonic, solution) `u`
against it gives, with every piece integrable,

`∫ ψ (a∇u · ∇v) + ∫ v (a∇u · ∇ψ) ≤ 0` (resp. `≥ 0`, `= 0`)

whenever `ψ ≥ 0` and `v ≥ 0` a.e. (no sign is needed for solutions).
The cutoff-squared versions (`ψ = η²`, `∇ψ = 2η∇η`) are exported as well.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-! ### Smooth compactly supported multipliers -/

theorem memLpOn_top_of_contDiff {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    MemLpOn U ⊤ ψ :=
  (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict U

theorem memLpOn_top_classicalGradient {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    MemLpOn U ⊤ (fun x => classicalGradient ψ x i) := by
  have hContinuous : Continuous (fun x => classicalGradient ψ x i) := by
    simpa only [classicalGradient_apply] using
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hCompact : HasCompactSupport (fun x => classicalGradient ψ x i) := by
    simpa only [classicalGradient_apply] using
      hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U

/-- The classical gradient of `η²`. -/
theorem classicalGradient_sq {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Vec d) :
    classicalGradient (fun y => η y ^ 2) x =
      (2 * η x) • classicalGradient η x := by
  have hηDiff : DifferentiableAt ℝ η x :=
    hη.contDiffAt.differentiableAt (by simp)
  funext i
  simp only [classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
  have hsquare : (fun y => η y ^ 2) = η * η := by
    funext y
    simp only [Pi.mul_apply, pow_two]
  rw [hsquare, fderiv_mul hηDiff hηDiff]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  ring

theorem contDiff_sq {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => η y ^ 2) :=
  hη.pow 2

theorem hasCompactSupport_sq {η : Vec d → ℝ} (hηc : HasCompactSupport η) :
    HasCompactSupport (fun y => η y ^ 2) := by
  have hsquare : (fun x => η x ^ 2) = η * η := by
    funext x
    simp only [Pi.mul_apply, pow_two]
  rw [hsquare]
  exact hηc.mul_right (f' := η)

theorem tsupport_sq_subset {η : Vec d → ℝ} (hηU : tsupport η ⊆ U) :
    tsupport (fun y => η y ^ 2) ⊆ U := by
  simpa only [pow_two] using
    (tsupport_mul_subset_left (f := η) (g := η)).trans hηU

/-! ### Splitting the tested flux -/

/-- Splitting an `L²` flux tested against the product `ψ v`: both pieces are
integrable and the integral splits. -/
theorem integral_vecDot_productTest (hU : IsOpenBoundedConvexDomain U)
    {F : Vec d → Vec d} (hF : MemVectorL2On U F) (v : H1Function U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => ψ x * vecDot (F x) (v.grad x)) U ∧
      IntegrableOn (fun x => v x * vecDot (F x) (classicalGradient ψ x)) U ∧
      ∫ x in U, vecDot (F x)
          ((v.mulContDiffHasCompactSupportToH10 hU hψ hψc hψU).toH1Function.grad x) =
        (∫ x in U, ψ x * vecDot (F x) (v.grad x)) +
          ∫ x in U, v x * vecDot (F x) (classicalGradient ψ x) := by
  have hψTop : MemLpOn U ⊤ ψ := memLpOn_top_of_contDiff hψ hψc
  have hDψTop (i : Fin d) : MemLpOn U ⊤ (fun x => classicalGradient ψ x i) :=
    memLpOn_top_classicalGradient hψ hψc i
  have hA : MemVectorL2On U (fun x => ψ x • v.grad x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (v.gradMemL2 i).fun_mul hψTop
  have hB : MemVectorL2On U (fun x => v x • classicalGradient ψ x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      v.memL2.fun_mul (hDψTop i)
  have hAint := integrableOn_vecDot_of_memVectorL2On hF hA
  have hBint := integrableOn_vecDot_of_memVectorL2On hF hB
  have hAeq : (fun x => vecDot (F x) (ψ x • v.grad x)) =
      fun x => ψ x * vecDot (F x) (v.grad x) := by
    funext x
    rw [vecDot_smul_right]
  have hBeq : (fun x => vecDot (F x) (v x • classicalGradient ψ x)) =
      fun x => v x * vecDot (F x) (classicalGradient ψ x) := by
    funext x
    rw [vecDot_smul_right]
  rw [hAeq] at hAint
  rw [hBeq] at hBint
  refine ⟨hAint, hBint, ?_⟩
  rw [H1Function.mulContDiffHasCompactSupportToH10_grad, ← integral_add hAint hBint]
  apply integral_congr_ae
  filter_upwards with x
  rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]

/-! ### Product tests of the three classes -/

/-- **Product test, subharmonic.** For `u` subharmonic, `v ∈ H¹` with
`v ≥ 0` a.e., and a smooth nonnegative multiplier `ψ` compactly supported in
`U`: `∫ ψ (a∇u·∇v) + ∫ v (a∇u·∇ψ) ≤ 0`, both pieces integrable. -/
theorem subharmonic_productTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v x)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      (∫ x in U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) ≤ 0 := by
  have hF := memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll
    u.gradMemL2
  obtain ⟨h1, h2, hsplit⟩ := integral_vecDot_productTest hU hF v hψ hψc hψU
  have hφ : (v.mulContDiffHasCompactSupportToH10 hU hψ hψc hψU).AENonnegative := by
    change ∀ᵐ x ∂volumeOn U, 0 ≤
      (v.mulContDiffHasCompactSupportToH10 hU hψ hψc hψU).toH1Function.toFun x
    rw [H1Function.mulContDiffHasCompactSupportToH10_toFun]
    filter_upwards [hv] with x hx
    exact mul_nonneg (hψ0 x) hx
  have htest := (subharmonic_test hU ha hEll hsub _ hφ).2
  exact ⟨h1, h2, hsplit ▸ htest⟩

/-- **Product test, superharmonic.** For `u` superharmonic, `v ≥ 0` a.e. and
`ψ ≥ 0` smooth compactly supported in `U`:
`0 ≤ ∫ ψ (a∇u·∇v) + ∫ v (a∇u·∇ψ)`, both pieces integrable. -/
theorem superharmonic_productTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v x)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      0 ≤ (∫ x in U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) := by
  have hF := memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll
    u.gradMemL2
  obtain ⟨h1, h2, hsplit⟩ := integral_vecDot_productTest hU hF v hψ hψc hψU
  have hφ : (v.mulContDiffHasCompactSupportToH10 hU hψ hψc hψU).AENonnegative := by
    change ∀ᵐ x ∂volumeOn U, 0 ≤
      (v.mulContDiffHasCompactSupportToH10 hU hψ hψc hψU).toH1Function.toFun x
    rw [H1Function.mulContDiffHasCompactSupportToH10_toFun]
    filter_upwards [hv] with x hx
    exact mul_nonneg (hψ0 x) hx
  have htest := (superharmonic_test hU ha hEll hsuper _ hφ).2
  exact ⟨h1, h2, hsplit ▸ htest⟩

/-- **Product test, solution.** For a homogeneous solution `u`, any `v ∈ H¹`
and any smooth `ψ` compactly supported in `U`:
`∫ ψ (a∇u·∇v) + ∫ v (a∇u·∇ψ) = 0`, both pieces integrable. -/
theorem solution_productTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (v : H1Function U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      (∫ x in U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) = 0 := by
  have hF := memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll
    u.gradMemL2
  obtain ⟨h1, h2, hsplit⟩ := integral_vecDot_productTest hU hF v hψ hψc hψU
  have htest := (solution_test hU ha hEll hsol
    (v.mulContDiffHasCompactSupportToH10 hU hψ hψc hψU)).2
  exact ⟨h1, h2, hsplit ▸ htest⟩

/-! ### Cutoff-squared versions -/

private theorem sq_cross_eq {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (v : H1Function U) (F : Vec d → Vec d) :
    (fun x => v x * vecDot (F x) (classicalGradient (fun y => η y ^ 2) x)) =
      fun x => 2 * η x * v x * vecDot (F x) (classicalGradient η x) := by
  funext x
  rw [classicalGradient_sq hη, vecDot_smul_right]
  ring

/-- **`η² v` test, subharmonic.** `∫ η² (a∇u·∇v) + ∫ 2ηv (a∇u·∇η) ≤ 0`. -/
theorem subharmonic_sqTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
        vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, 2 * η x * v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) ≤ 0 := by
  have h := subharmonic_productTest hU ha hEll hsub v hv (contDiff_sq hη)
    (hasCompactSupport_sq hηc) (tsupport_sq_subset hηU) (fun x => sq_nonneg (η x))
  rw [sq_cross_eq hη] at h
  exact h

/-- **`η² v` test, superharmonic.** `0 ≤ ∫ η² (a∇u·∇v) + ∫ 2ηv (a∇u·∇η)`. -/
theorem superharmonic_sqTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v x)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
        vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      0 ≤ (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, 2 * η x * v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) := by
  have h := superharmonic_productTest hU ha hEll hsuper v hv (contDiff_sq hη)
    (hasCompactSupport_sq hηc) (tsupport_sq_subset hηU) (fun x => sq_nonneg (η x))
  rw [sq_cross_eq hη] at h
  exact h

/-- **`η² v` test, solution.** `∫ η² (a∇u·∇v) + ∫ 2ηv (a∇u·∇η) = 0`. -/
theorem solution_sqTest (hU : IsOpenBoundedConvexDomain U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U}
    (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (v : H1Function U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
        vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, 2 * η x * v x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) = 0 := by
  have h := solution_productTest hU ha hEll hsol v (contDiff_sq hη)
    (hasCompactSupport_sq hηc) (tsupport_sq_subset hηU)
  rw [sq_cross_eq hη] at h
  exact h

end DGNM

end PDE
