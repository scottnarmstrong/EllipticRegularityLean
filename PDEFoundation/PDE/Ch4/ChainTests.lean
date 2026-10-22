module

public import PDEFoundation.PDE.Ch4.Absorb
public import PDEFoundation.PDE.Ch4.Composites
public import PDEFoundation.PDE.DGNM.ChainTests

/-!
# Chain-rule tests and the logarithmic energy estimate on bounded open sets

Open-set / Lipschitz-cutoff versions of `PDE.DGNM.subharmonic_chainTest`,
`superharmonic_chainTest`, `superharmonic_log_energy` and `superharmonic_log_energy_euclidean`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

private theorem chain_main_eq {u v : H1Function U} {G' : ℝ → ℝ}
    (hvgrad : ∀ x, v.grad x = G' (u x) • u.grad x) (η : Vec d → ℝ) :
    (fun x => η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) =
      fun x => η x ^ 2 * G' (u x) * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  funext x
  rw [hvgrad, DGNM.vecDot_smul_right, vecDot_comm (matVecMul (a x) (u.grad x))]
  ring

/-- **Chain-rule test, superharmonic**, on a bounded open set with a Lipschitz cutoff. -/
theorem superharmonic_chainTest_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    (v : H1Function U) (G' : ℝ → ℝ) (hvgrad : ∀ x, v.grad x = G' (u.toFun x) • u.grad x)
    (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * G' (u.toFun x) *
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U ∧
      IntegrableOn (fun x => 2 * η x * v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      0 ≤ (∫ x in U, η x ^ 2 * G' (u.toFun x) *
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
          ∫ x in U, 2 * η x * v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) := by
  have h := superharmonic_sqTest_lip hU hfin ha hEll hsuper v hv hη hL hM hηc hηU
  rw [chain_main_eq hvgrad] at h
  exact h

/-- **Chain-rule test, subharmonic.** -/
theorem subharmonic_chainTest_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u)
    (v : H1Function U) (G' : ℝ → ℝ) (hvgrad : ∀ x, v.grad x = G' (u.toFun x) • u.grad x)
    (hv : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 * G' (u.toFun x) *
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) U ∧
      IntegrableOn (fun x => 2 * η x * v.toFun x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x)) U ∧
      (∫ x in U, η x ^ 2 * G' (u.toFun x) *
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
          ∫ x in U, 2 * η x * v.toFun x *
            vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) ≤ 0 := by
  have h := subharmonic_sqTest_lip hU hfin ha hEll hsub v hv hη hL hM hηc hηU
  rw [chain_main_eq hvgrad] at h
  exact h

theorem memVectorL2On_classicalGradient_lip {L : ℝ} {η : Vec d → ℝ} (hη : EucLip L η)
    (hL : 0 ≤ L) (hηc : HasCompactSupport η) : MemVectorL2On U (classicalGradient η) := fun i => by
  refine MemLp.restrict U ?_
  exact memLp_two_of_bounded_of_zero_off (C := L) hηc.isCompact
    (EucLip.aestronglyMeasurable_partialDeriv i) (hη.ae_abs_partialDeriv_le hL i)
    (fun x hx => by simp [classicalGradient, fderiv_of_notMem_tsupport ℝ hx])

/-- **Logarithmic energy estimate.** For a supersolution `u ≥ δ > 0` a.e. on a bounded open
set, `∫ η² ∇log u · a ∇log u ≤ 4Λ ∫ |∇η|²` with `∇ log u = u⁻¹ ∇u`. -/
theorem superharmonic_log_energy_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u.toFun x)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecDot ((u.toFun x)⁻¹ • u.grad x)
        (matVecMul (a x) ((u.toFun x)⁻¹ • u.grad x)) ≤
      4 * Λ * ∫ x in U, vecNormSq (classicalGradient η x) := by
  set v := invOfLowerBoundOpen hU hfin u hδ hu
  set w := logOfLowerBoundOpen hU hfin u hδ hu
  have hv0 : ∀ᵐ x ∂volumeOn U, 0 ≤ v.toFun x := hu.mono fun x hx => by
    change 0 ≤ (u.toFun x)⁻¹
    exact inv_nonneg.mpr (hδ.le.trans hx)
  obtain ⟨h1, h2, hle⟩ := superharmonic_chainTest_open hU hfin ha hEll hsuper v
    (fun t => -(t ^ 2)⁻¹) (fun _ => rfl) hv0 hη hL hM hηc hηU
  set ξ : Vec d → Vec d := fun x => (u.toFun x)⁻¹ • u.grad x with hξdef
  have hξ : MemVectorL2On U ξ := w.gradMemL2
  have hmain : ∫ x in U, η x ^ 2 * (fun t => -(t ^ 2)⁻¹) (u.toFun x) *
      vecDot (u.grad x) (matVecMul (a x) (u.grad x)) =
      -∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    simp only [hξdef, DGNM.matVecMul_smul, DGNM.vecDot_smul_left, DGNM.vecDot_smul_right]
    by_cases h0 : u.toFun x = 0
    · simp [h0]
    · field_simp
  have hcross : ∫ x in U, 2 * η x * v.toFun x *
      vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η x) =
      2 * ∫ x in U, η x * (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [hξdef, DGNM.matVecMul_smul, DGNM.vecDot_smul_left]
    change 2 * η x * (u.toFun x)⁻¹ * _ = _
    ring
  rw [hmain, hcross] at hle
  have htest : 1 * (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      (-2) * (∫ x in U, η x * (fun _ => (1 : ℝ)) x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0 := by
    linarith
  have hωη : MemVectorL2On U (fun x => (fun _ => (1 : ℝ)) x • classicalGradient η x) := by
    simpa only [one_smul] using memVectorL2On_classicalGradient_lip (U := U) hη hL hηc
  have habs := absorb_open hU.measurableSet ha hEll hξ (hη.continuous hL) hM hωη one_pos htest
  simpa only [one_pow, one_mul, div_one, neg_sq, show (2 : ℝ) ^ 2 = 4 by norm_num]
    using habs

/-- **Logarithmic energy estimate, Euclidean form.** `∫ η² |u⁻¹ ∇u|² ≤ 4Λ ∫ |∇η|²`. -/
theorem superharmonic_log_energy_euclidean_open (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function U} (hsuper : IsWeakDivergenceFormSuperharmonicOn a U u)
    {δ : ℝ} (hδ : 0 < δ) (hu : ∀ᵐ x ∂volumeOn U, δ ≤ u.toFun x)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ x in U, η x ^ 2 * vecNormSq ((u.toFun x)⁻¹ • u.grad x) ≤
      4 * Λ * ∫ x in U, vecNormSq (classicalGradient η x) := by
  have hE := superharmonic_log_energy_open hU hfin ha hEll hsuper hδ hu hη hL hM hηc hηU
  set w := logOfLowerBoundOpen hU hfin u hδ hu
  have hηcont : Continuous η := hη.continuous hL
  have hξ : MemVectorL2On U (fun x => (u.toFun x)⁻¹ • u.grad x) := w.gradMemL2
  have hA : MemVectorL2On U (fun x => η x • ((u.toFun x)⁻¹ • u.grad x)) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξ i) (hη.continuous hL) hM
  have hint1 : IntegrableOn (fun x => η x ^ 2 * vecNormSq ((u.toFun x)⁻¹ • u.grad x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hA
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU.measurableSet ha hEll hξ
  have hint2 : IntegrableOn (fun x => η x ^ 2 * vecDot ((u.toFun x)⁻¹ • u.grad x)
      (matVecMul (a x) ((u.toFun x)⁻¹ • u.grad x))) U := by
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ((u.toFun x)⁻¹ • u.grad x)) := fun i => by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        memL2On_mul_bounded (hξ i) (by fun_prop : Continuous fun x => η x ^ 2) (abs_sq_le hM)
    simpa only [DGNM.vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  refine le_trans (setIntegral_mono_on hint1 hint2 hU.measurableSet fun x hx => ?_) hE
  exact mul_le_mul_of_nonneg_left (DGNM.vecNormSq_le_vecDot_matVecMul (hEll x hx) _)
    (sq_nonneg _)

end PDE.Ch4Infra
