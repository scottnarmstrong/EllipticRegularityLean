module

public import PDEFoundation.Sobolev.Ch4.LipschitzTest
public import PDEFoundation.Sobolev.H1.Pairing

/-!
# Product of an `H¹` function with a Lipschitz function

For `u ∈ H¹(U)` and a bounded Euclidean-Lipschitz function `η`, the product `η u` is in `H¹(U)`
with gradient `η ∇u + u ∇η`, where `∇η` is the a.e. classical gradient (Rademacher), bounded by
the Lipschitz constant in Euclidean length.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set Filter

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)}

theorem memLp_two_of_bounded_of_zero_off {F : Vec d → ℝ} {C : ℝ} {K : Set (Vec d)}
    (hK : IsCompact K) (hF : AEStronglyMeasurable F volume)
    (hC : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖F x‖ ≤ C) (hz : ∀ x, x ∉ K → F x = 0) :
    MemLp F 2 volume := by
  have hind : F = K.indicator F := by
    funext x
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hz x hx]
  rw [hind, memLp_indicator_iff_restrict hK.isClosed.measurableSet]
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact MemLp.of_bound (hF.mono_measure Measure.restrict_le_self) C (ae_restrict_of_ae hC)

/-- The coordinate derivatives of a Euclidean-Lipschitz function are a.e. bounded by `L`. -/
theorem EucLip.ae_abs_partialDeriv_le {L : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L)
    (i : Fin d) : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖fderiv ℝ η x (basisVec i)‖ ≤ L := by
  filter_upwards [hη.ae_differentiableAt hL] with x hx
  exact (Real.norm_eq_abs _ ▸ hη.abs_partialDeriv_le hL hx i)

theorem EucLip.aestronglyMeasurable_partialDeriv {η : Vec d → ℝ} (i : Fin d) :
    AEStronglyMeasurable (fun x => fderiv ℝ η x (basisVec i)) volume :=
  (measurable_fderiv_apply_const ℝ η (basisVec i)).aestronglyMeasurable

/-- The product `η φ` of a Lipschitz function with a smooth compactly supported one, together
with the a.e. product rule. -/
theorem integral_mul_partial_product (hU : IsOpen U) (u : H1Function U)
    {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (i : Fin d) :
    ∫ x in U, (η x * u.toFun x) * fderiv ℝ φ x (basisVec i) =
      -∫ x in U, (η x * u.grad x i + u.toFun x * fderiv ℝ η x (basisVec i)) * φ x := by
  have hηc : Continuous η := hη.continuous hL
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Kφ, hKφ0, hKφ⟩ := EucLip.of_contDiff_hasCompactSupport (hφ.of_le (by simp)) hφc
  obtain ⟨Bφ, hBφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hBφ' : ∀ x, |φ x| ≤ Bφ := fun x => by simpa using hBφ x
  have hψ : EucLip (M * Kφ + Bφ * L) (fun x => η x * φ x) := hη.mul hKφ hM hBφ'
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hBnn : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ' 0)
  have hψc : HasCompactSupport (fun x => η x * φ x) := hφc.mul_left
  have hψU : tsupport (fun x => η x * φ x) ⊆ U :=
    (tsupport_mul_subset_right (f := η) (g := φ)).trans hφU
  have hmain := H1Function.integral_mul_partial_lip_eq hU u hψ
    (by positivity) hψc hψU i
  set Dφ : Vec d → ℝ := fun x => fderiv ℝ φ x (basisVec i) with hDφ
  set Dη : Vec d → ℝ := fun x => fderiv ℝ η x (basisVec i) with hDη
  have hDφc : Continuous Dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφcs : HasCompactSupport Dφ := by
    simpa [hDφ] using hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  -- the a.e. product rule
  have hprod : ∀ᵐ x ∂(volume : Measure (Vec d)),
      fderiv ℝ (fun x => η x * φ x) x (basisVec i) = η x * Dφ x + φ x * Dη x := by
    filter_upwards [hη.ae_differentiableAt hL] with x hx
    rw [fderiv_fun_mul hx (hφ.differentiable (by simp) x)]
    simp [hDφ, hDη]
  -- integrability
  have hφDη : MemL2On U (fun x => φ x * Dη x) := by
    refine MemLp.restrict U ?_
    refine memLp_two_of_bounded_of_zero_off (C := Bφ * L) hφc.isCompact
      (hφcont.aestronglyMeasurable.mul (EucLip.aestronglyMeasurable_partialDeriv i))
      ?_ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    filter_upwards [hη.ae_abs_partialDeriv_le hL i] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hBφ' x) (by simpa using hx) (norm_nonneg _) hBnn
  have hηDφ : MemL2On U (fun x => η x * Dφ x) :=
    ((hηc.mul hDφc).memLp_of_hasCompactSupport hDφcs.mul_left).restrict U
  have hηφ : MemL2On U (fun x => η x * φ x) :=
    ((hηc.mul hφcont).memLp_of_hasCompactSupport hφc.mul_left).restrict U
  have hDηφ : MemL2On U (fun x => Dη x * φ x) := by
    refine MemLp.restrict U ?_
    refine memLp_two_of_bounded_of_zero_off (C := L * Bφ) hφc.isCompact
      ((EucLip.aestronglyMeasurable_partialDeriv i).mul hφcont.aestronglyMeasurable)
      ?_ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    filter_upwards [hη.ae_abs_partialDeriv_le hL i] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa using hx) (hBφ' x) (norm_nonneg _) hL
  have I1 : IntegrableOn (fun x => u.toFun x * (η x * Dφ x)) U :=
    integrableOn_mul_of_memL2On u.memL2 hηDφ
  have I2 : IntegrableOn (fun x => u.toFun x * (φ x * Dη x)) U :=
    integrableOn_mul_of_memL2On u.memL2 hφDη
  have I3 : IntegrableOn (fun x => u.grad x i * (η x * φ x)) U :=
    integrableOn_mul_of_memL2On (u.grad_memL2 i) hηφ
  have I4 : IntegrableOn (fun x => u.toFun x * Dη x * φ x) U := by
    simpa [mul_assoc] using integrableOn_mul_of_memL2On u.memL2 hDηφ
  have I5 : IntegrableOn (fun x => η x * u.grad x i * φ x) U := by
    simpa [mul_assoc] using I3.congr_fun (fun x _ => by ring) hU.measurableSet
  -- combine
  have e1 : ∫ x in U, u.toFun x * fderiv ℝ (fun x => η x * φ x) x (basisVec i) =
      ∫ x in U, (u.toFun x * (η x * Dφ x) + u.toFun x * (φ x * Dη x)) := by
    refine setIntegral_congr_ae hU.measurableSet ?_
    filter_upwards [hprod] with x hx _
    rw [hx]; ring
  rw [e1, integral_add I1 I2] at hmain
  have e2 : ∫ x in U, (η x * u.toFun x) * Dφ x = ∫ x in U, u.toFun x * (η x * Dφ x) :=
    setIntegral_congr_fun hU.measurableSet fun x _ => by ring
  have e3 : ∫ x in U, u.grad x i * (η x * φ x) = ∫ x in U, η x * u.grad x i * φ x :=
    setIntegral_congr_fun hU.measurableSet fun x _ => by ring
  have e4 : ∫ x in U, (η x * u.grad x i + u.toFun x * Dη x) * φ x =
      (∫ x in U, η x * u.grad x i * φ x) + ∫ x in U, u.toFun x * (φ x * Dη x) := by
    rw [← integral_add I5 I2]
    exact setIntegral_congr_fun hU.measurableSet fun x _ => by ring
  rw [e2, e4]
  rw [e3] at hmain
  linarith

theorem mulLip_memL2 (u : H1Function U) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η)
    (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) : MemL2On U (fun x => η x * u.toFun x) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (u.memL2.const_mul M).mono
    ((hη.continuous hL).aestronglyMeasurable.mul u.memL2.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hMnn]
  exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)

theorem mulLip_gradMemL2 (u : H1Function U) {L M : ℝ} {η : Vec d → ℝ} (hη : EucLip L η)
    (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) (i : Fin d) :
    MemL2On U (fun x => η x * u.grad x i + u.toFun x * fderiv ℝ η x (basisVec i)) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine MemLp.add ?_ ?_
  · refine ((u.grad_memL2 i).const_mul M).mono
      ((hη.continuous hL).aestronglyMeasurable.mul (u.grad_memL2 i).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hMnn]
    exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
  · refine (u.memL2.const_mul L).mono
      (u.memL2.aestronglyMeasurable.mul
        ((EucLip.aestronglyMeasurable_partialDeriv i).mono_measure Measure.restrict_le_self))
      ?_
    have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖fderiv ℝ η x (basisVec i)‖ ≤ L :=
      hη.ae_abs_partialDeriv_le hL i
    have hae' : ∀ᵐ x ∂(volumeOn U), ‖fderiv ℝ η x (basisVec i)‖ ≤ L :=
      ae_restrict_of_ae hae
    filter_upwards [hae'] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hL] at hx ⊢
    rw [mul_comm L]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- **Product of an `H¹` function with a bounded Lipschitz function.**  The value is `η u`, the
gradient is `η ∇u + u ∇η` with `∇η` the a.e. classical gradient of `η`. -/
noncomputable def mulLip (hU : IsOpen U) (u : H1Function U) {L M : ℝ}
    {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) : H1Function U where
  toFun := fun x => η x * u.toFun x
  grad := fun x => η x • u.grad x + u.toFun x • classicalGradient η x
  memL2 := mulLip_memL2 u hη hL hM
  gradMemL2 := fun i => by
    simpa [classicalGradient] using mulLip_gradMemL2 u hη hL hM i
  hasWeakGradient := fun i φ hφ hφc hφU => by
    simpa [classicalGradient] using integral_mul_partial_product hU u hη hL hM hφ hφc hφU i

@[simp] theorem mulLip_toFun (hU : IsOpen U) (u : H1Function U) {L M : ℝ}
    {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) :
    (mulLip hU u hη hL hM).toFun = fun x => η x * u.toFun x := rfl

@[simp] theorem mulLip_grad (hU : IsOpen U) (u : H1Function U) {L M : ℝ}
    {η : Vec d → ℝ} (hη : EucLip L η) (hL : 0 ≤ L) (hM : ∀ x, |η x| ≤ M) :
    (mulLip hU u hη hL hM).grad =
      fun x => η x • u.grad x + u.toFun x • classicalGradient η x := rfl

end PDE.Ch4Infra
