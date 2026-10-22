module

public import PDEFoundation

/-!
# Derivatives and smooth multiples of test functions; the curl pairing

For `v ∈ H¹(U)` and a smooth compactly supported `ψ`, the pairing of `∇v` with the divergence-free
field `χ R∇ψ` (`R` the rotation in the `(i0, i1)` plane) is computed by the weak gradient of `v`.
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {U : Set (Vec d)}

/-- A coordinate derivative of a test function is again a test function. -/
noncomputable def testDeriv (φ : WeakTestFunction U) (j : Fin d) : WeakTestFunction U where
  toFun := euclideanCoordDeriv j φ.toFun
  contDiff := contDiff_euclideanCoordDeriv φ.contDiff j
  hasCompactSupport := φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec j)
  tsupport_subset :=
    (tsupport_euclideanCoordDeriv_subset_tsupport j φ.toFun).trans φ.tsupport_subset

theorem testDeriv_apply (φ : WeakTestFunction U) (j : Fin d) (x : Vec d) :
    testDeriv φ j x = φ.partialDeriv j x := rfl

theorem testDeriv_partialDeriv_comm (φ : WeakTestFunction U) (i j : Fin d) (x : Vec d) :
    (testDeriv φ j).partialDeriv i x = (testDeriv φ i).partialDeriv j x :=
  euclideanCoordSecondDeriv_comm_of_contDiffAt φ.contDiff.contDiffAt j i

/-- A smooth multiple of a test function. -/
noncomputable def testMul (φ : WeakTestFunction U) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : WeakTestFunction U where
  toFun := fun x => χ x * φ x
  contDiff := hχ.mul φ.contDiff
  hasCompactSupport := φ.hasCompactSupport.mul_left
  tsupport_subset := (tsupport_mul_subset_right).trans φ.tsupport_subset

theorem testMul_apply (φ : WeakTestFunction U) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (x : Vec d) : testMul φ hχ x = χ x * φ x := rfl

theorem testMul_partialDeriv (φ : WeakTestFunction U) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (i : Fin d) (x : Vec d) :
    (testMul φ hχ).partialDeriv i x =
      fderiv ℝ χ x (basisVec i) * φ x + χ x * φ.partialDeriv i x := by
  have h1 : DifferentiableAt ℝ χ x := hχ.differentiable (by simp) x
  have h2 : DifferentiableAt ℝ φ.toFun x := φ.contDiff.differentiable (by simp) x
  unfold WeakTestFunction.partialDeriv
  change fderiv ℝ (χ * φ.toFun) x (basisVec i) = _
  rw [fderiv_mul h1 h2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Curl pairing.**  For `v ∈ H¹(U)`, a smooth `χ` and a test function `ψ`,
`∫ (∂_{i1}v · χ ∂_{i0}ψ - ∂_{i0}v · χ ∂_{i1}ψ) = ∫ v (∂_{i0}χ ∂_{i1}ψ - ∂_{i1}χ ∂_{i0}ψ)`. -/
theorem curl_pairing (v : H1Function U) (i0 i1 : Fin d) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ψ : WeakTestFunction U) :
    ∫ x in U, (v.grad x i1 * (χ x * ψ.partialDeriv i0 x) -
        v.grad x i0 * (χ x * ψ.partialDeriv i1 x)) =
      ∫ x in U, v.toFun x * (fderiv ℝ χ x (basisVec i0) * ψ.partialDeriv i1 x -
        fderiv ℝ χ x (basisVec i1) * ψ.partialDeriv i0 x) := by
  let T0 := testMul (testDeriv ψ i0) hχ
  let T1 := testMul (testDeriv ψ i1) hχ
  have hw0 := hasWeakPartialDerivOn_iff_forall_testFunction.mp (v.hasWeakPartialDerivOn i1) T0
  have hw1 := hasWeakPartialDerivOn_iff_forall_testFunction.mp (v.hasWeakPartialDerivOn i0) T1
  have hint0 : Integrable (fun x => v.grad x i1 * T0 x) (volume.restrict U) :=
    (v.gradMemL2 i1).integrable_mul (T0.memLp_toFun 2)
  have hint1 : Integrable (fun x => v.grad x i0 * T1 x) (volume.restrict U) :=
    (v.gradMemL2 i0).integrable_mul (T1.memLp_toFun 2)
  have hv0 : Integrable (fun x => v.toFun x * T0.partialDeriv i1 x) (volume.restrict U) :=
    v.memL2.integrable_mul (T0.memLp_partialDeriv i1 2)
  have hv1 : Integrable (fun x => v.toFun x * T1.partialDeriv i0 x) (volume.restrict U) :=
    v.memL2.integrable_mul (T1.memLp_partialDeriv i0 2)
  have hL : (∫ x in U, (v.grad x i1 * (χ x * ψ.partialDeriv i0 x) -
        v.grad x i0 * (χ x * ψ.partialDeriv i1 x))) =
      (∫ x in U, v.grad x i1 * T0 x) - ∫ x in U, v.grad x i0 * T1 x := by
    rw [← integral_sub hint0 hint1]
    rfl
  rw [hL]
  have hR : (∫ x in U, v.toFun x * (fderiv ℝ χ x (basisVec i0) * ψ.partialDeriv i1 x -
        fderiv ℝ χ x (basisVec i1) * ψ.partialDeriv i0 x)) =
      (∫ x in U, v.toFun x * T1.partialDeriv i0 x) -
        ∫ x in U, v.toFun x * T0.partialDeriv i1 x := by
    rw [← integral_sub hv1 hv0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    have e1 : T1.partialDeriv i0 x = fderiv ℝ χ x (basisVec i0) * ψ.partialDeriv i1 x +
        χ x * (testDeriv ψ i1).partialDeriv i0 x := testMul_partialDeriv _ hχ i0 x
    have e0 : T0.partialDeriv i1 x = fderiv ℝ χ x (basisVec i1) * ψ.partialDeriv i0 x +
        χ x * (testDeriv ψ i0).partialDeriv i1 x := testMul_partialDeriv _ hχ i1 x
    rw [e1, e0, testDeriv_partialDeriv_comm ψ i1 i0 x]
    ring
  rw [hR, hw0, hw1]
  ring

/-- The zero form of the curl pairing. -/
theorem curl_pairing_zero (v : H1Function U) (i0 i1 : Fin d) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ψ : WeakTestFunction U) :
    ∫ x in U, (v.grad x i1 * (χ x * ψ.partialDeriv i0 x) -
        v.grad x i0 * (χ x * ψ.partialDeriv i1 x) +
        v.toFun x * (fderiv ℝ χ x (basisVec i1) * ψ.partialDeriv i0 x -
          fderiv ℝ χ x (basisVec i0) * ψ.partialDeriv i1 x)) = 0 := by
  let T0 := testMul (testDeriv ψ i0) hχ
  let T1 := testMul (testDeriv ψ i1) hχ
  have hw0 := hasWeakPartialDerivOn_iff_forall_testFunction.mp (v.hasWeakPartialDerivOn i1) T0
  have hw1 := hasWeakPartialDerivOn_iff_forall_testFunction.mp (v.hasWeakPartialDerivOn i0) T1
  have hint0 : Integrable (fun x => v.grad x i1 * T0 x) (volume.restrict U) :=
    (v.gradMemL2 i1).integrable_mul (T0.memLp_toFun 2)
  have hint1 : Integrable (fun x => v.grad x i0 * T1 x) (volume.restrict U) :=
    (v.gradMemL2 i0).integrable_mul (T1.memLp_toFun 2)
  have hv0 : Integrable (fun x => v.toFun x * T0.partialDeriv i1 x) (volume.restrict U) :=
    v.memL2.integrable_mul (T0.memLp_partialDeriv i1 2)
  have hv1 : Integrable (fun x => v.toFun x * T1.partialDeriv i0 x) (volume.restrict U) :=
    v.memL2.integrable_mul (T1.memLp_partialDeriv i0 2)
  have hpt : ∀ x, (v.grad x i1 * (χ x * ψ.partialDeriv i0 x) -
        v.grad x i0 * (χ x * ψ.partialDeriv i1 x) +
        v.toFun x * (fderiv ℝ χ x (basisVec i1) * ψ.partialDeriv i0 x -
          fderiv ℝ χ x (basisVec i0) * ψ.partialDeriv i1 x)) =
      ((v.grad x i1 * T0 x + v.toFun x * T0.partialDeriv i1 x) -
        (v.grad x i0 * T1 x + v.toFun x * T1.partialDeriv i0 x)) := by
    intro x
    have e1 : T1.partialDeriv i0 x = fderiv ℝ χ x (basisVec i0) * ψ.partialDeriv i1 x +
        χ x * (testDeriv ψ i1).partialDeriv i0 x := testMul_partialDeriv _ hχ i0 x
    have e0 : T0.partialDeriv i1 x = fderiv ℝ χ x (basisVec i1) * ψ.partialDeriv i0 x +
        χ x * (testDeriv ψ i0).partialDeriv i1 x := testMul_partialDeriv _ hχ i1 x
    rw [e1, e0, testDeriv_partialDeriv_comm ψ i1 i0 x]
    have hT0 : T0.toFun x = χ x * ψ.partialDeriv i0 x := rfl
    have hT1 : T1.toFun x = χ x * ψ.partialDeriv i1 x := rfl
    rw [hT0, hT1]
    ring
  simp_rw [hpt]
  have hA : Integrable (fun x => v.grad x i1 * T0 x + v.toFun x * T0.partialDeriv i1 x)
      (volume.restrict U) := hint0.add hv0
  have hB : Integrable (fun x => v.grad x i0 * T1 x + v.toFun x * T1.partialDeriv i0 x)
      (volume.restrict U) := hint1.add hv1
  rw [integral_sub hA hB, integral_add hint0 hv0, integral_add hint1 hv1, hw0, hw1]
  ring

end PDE.Ch4Meyers
