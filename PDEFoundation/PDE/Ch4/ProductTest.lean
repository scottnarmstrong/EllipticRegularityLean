module

public import PDEFoundation.PDE.Ch4.CompactTests

/-!
# Product tests `ψ v` with Lipschitz multipliers on bounded open sets

Generalization of `PDE.DGNM.subharmonic_productTest` (smooth `ψ`, convex `U`): the multiplier
`ψ` is a bounded Euclidean-Lipschitz function with compact support in the bounded open set `U`
(`classicalGradient ψ` is its a.e. gradient), and `v ∈ H¹(U)` is arbitrary.
The cutoff-squared versions `ψ = η²` are exported as well.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

theorem memL2On_mul_bounded {g ψ : Vec d → ℝ} {M : ℝ} (hg : MemL2On U g) (hψc : Continuous ψ)
    (hM : ∀ x, |ψ x| ≤ M) : MemL2On U (fun x => ψ x * g x) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (hg.const_mul M).mono (hψc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hMnn]
  exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)

theorem memL2On_mul_partialDeriv {v η : Vec d → ℝ} {L : ℝ} (hη : EucLip L η) (hL : 0 ≤ L)
    (hv : MemL2On U v) (i : Fin d) : MemL2On U (fun x => v x * fderiv ℝ η x (basisVec i)) := by
  refine (hv.const_mul L).mono
    (hv.aestronglyMeasurable.mul
      ((EucLip.aestronglyMeasurable_partialDeriv i).mono_measure Measure.restrict_le_self)) ?_
  have hae' : ∀ᵐ x ∂(volumeOn U), ‖fderiv ℝ η x (basisVec i)‖ ≤ L :=
    ae_restrict_of_ae (hη.ae_abs_partialDeriv_le hL i)
  filter_upwards [hae'] with x hx
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hL] at hx ⊢
  rw [mul_comm L]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- Splitting an `L²` flux tested against the product `ψ v`. -/
theorem integral_vecDot_productTest_lip (hU : IsOpen U) {F : Vec d → Vec d}
    (hF : MemVectorL2On U F) (v : H1Function U) {L M : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ)
    (hL : 0 ≤ L) (hM : ∀ x, |ψ x| ≤ M) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => ψ x * vecDot (F x) (v.grad x)) U ∧
      IntegrableOn (fun x => v.toFun x * vecDot (F x) (classicalGradient ψ x)) U ∧
      ∫ x in U, vecDot (F x) ((mulLipH10 hU v hψ hL hM hψc hψU).toH1Function.grad x) =
        (∫ x in U, ψ x * vecDot (F x) (v.grad x)) +
          ∫ x in U, v.toFun x * vecDot (F x) (classicalGradient ψ x) := by
  have hA : MemVectorL2On U (fun x => ψ x • v.grad x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      memL2On_mul_bounded (v.gradMemL2 i) (hψ.continuous hL) hM
  have hB : MemVectorL2On U (fun x => v.toFun x • classicalGradient ψ x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      memL2On_mul_partialDeriv hψ hL v.memL2 i
  have hAint := integrableOn_vecDot_of_memVectorL2On hF hA
  have hBint := integrableOn_vecDot_of_memVectorL2On hF hB
  have hAeq : (fun x => vecDot (F x) (ψ x • v.grad x)) =
      fun x => ψ x * vecDot (F x) (v.grad x) := by
    funext x; rw [DGNM.vecDot_smul_right]
  have hBeq : (fun x => vecDot (F x) (v.toFun x • classicalGradient ψ x)) =
      fun x => v.toFun x * vecDot (F x) (classicalGradient ψ x) := by
    funext x; rw [DGNM.vecDot_smul_right]
  rw [hAeq] at hAint
  rw [hBeq] at hBint
  refine ⟨hAint, hBint, ?_⟩
  rw [mulLipH10_toH1Function, mulLip_grad, ← integral_add hAint hBint]
  apply integral_congr_ae
  filter_upwards with x
  rw [DGNM.vecDot_add_right, DGNM.vecDot_smul_right, DGNM.vecDot_smul_right]

theorem aeNonnegative_mulLipH10 (hU : IsOpen U) (v : H1Function U) {L M : ℝ} {ψ : Vec d → ℝ}
    (hψ : EucLip L ψ) (hL : 0 ≤ L) (hM : ∀ x, |ψ x| ≤ M) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x) (hψ0 : ∀ x, 0 ≤ ψ x) :
    (mulLipH10 hU v hψ hL hM hψc hψU).AENonnegative := by
  change ∀ᵐ x ∂volumeOn U, 0 ≤ (mulLip hU v hψ hL hM).toFun x
  filter_upwards [hv] with x hx
  exact mul_nonneg (hψ0 x) hx

/-- **Product test, subharmonic**, Lipschitz multiplier, bounded open set. -/
theorem subharmonic_productTest_lip (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x)
    {L M : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hM : ∀ x, |ψ x| ≤ M)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      (∫ x in U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) ≤ 0 := by
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll u.gradMemL2
  obtain ⟨h1, h2, hsplit⟩ := integral_vecDot_productTest_lip hU hF v hψ hL hM hψc hψU
  have htest := (subharmonic_test_open hU hfin ha hEll hsub _
    (aeNonnegative_mulLipH10 hU v hψ hL hM hψc hψU hv hψ0)).2
  exact ⟨h1, h2, hsplit ▸ htest⟩

/-- **Product test, superharmonic.** -/
theorem superharmonic_productTest_lip (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (v : H1Function U) (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x)
    {L M : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hM : ∀ x, |ψ x| ≤ M)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (hψ0 : ∀ x, 0 ≤ ψ x) :
    IntegrableOn (fun x => ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      0 ≤ (∫ x in U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) := by
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll u.gradMemL2
  obtain ⟨h1, h2, hsplit⟩ := integral_vecDot_productTest_lip hU hF v hψ hL hM hψc hψU
  have htest := (superharmonic_test_open hU hfin ha hEll hsuper _
    (aeNonnegative_mulLipH10 hU v hψ hL hM hψc hψU hv hψ0)).2
  exact ⟨h1, h2, hsplit ▸ htest⟩

/-- **Product test, solution** (any open set, any sign). -/
theorem solution_productTest_lip (hU : IsOpen U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsol : IsWeakDivergenceFormSolutionOn a U u (0 : Vec d → ℝ) 0)
    (v : H1Function U)
    {L M : ℝ} {ψ : Vec d → ℝ} (hψ : EucLip L ψ) (hL : 0 ≤ L) (hM : ∀ x, |ψ x| ≤ M)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x)) U ∧
      (∫ x in U, ψ x * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
          ∫ x in U, v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient ψ x) = 0 := by
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll u.gradMemL2
  obtain ⟨h1, h2, hsplit⟩ := integral_vecDot_productTest_lip hU hF v hψ hL hM hψc hψU
  have htest := (solution_test_open hU ha hEll hsol (mulLipH10 hU v hψ hL hM hψc hψU)).2
  exact ⟨h1, h2, hsplit ▸ htest⟩

end PDE.Ch4Infra
