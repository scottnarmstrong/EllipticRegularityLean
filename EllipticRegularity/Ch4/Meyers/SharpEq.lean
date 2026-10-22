module

public import EllipticRegularity.Ch4.Meyers.Sharp

/-!
# The planar-type example: the weak equation `-div a∇u = 0`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {i0 i1 : Fin d}

/-- The exponent `γ = (1/√Λ - 1)/2` of the planar-type example. -/
noncomputable def sharpγ (Λ : ℝ) : ℝ := (1 / Real.sqrt Λ - 1) / 2

theorem sharpγ_gt {Λ : ℝ} (hΛ : 1 < Λ) : -1 / 2 < sharpγ Λ := by
  unfold sharpγ
  have : 0 < 1 / Real.sqrt Λ := by
    have : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
    positivity
  linarith

theorem sharpγ_lt {Λ : ℝ} (hΛ : 1 < Λ) : sharpγ Λ < 0 := by
  unfold sharpγ
  have h1 : 1 < Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hΛ
  have : 1 / Real.sqrt Λ < 1 := by rw [div_lt_one (by linarith)]; exact h1
  linarith

/-- The `H¹` function `u = s^γ x_{i0}` of the planar-type example. -/
noncomputable def sharpU (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    H1Function (euclideanBall (0 : Vec d) 1) :=
  profH1 (sharpW_01 i0 i1) hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1) (sharpW_i0 i0 i1)
    (sharpγ_gt hΛ) (sharpγ_lt hΛ).le

/-- The companion `H¹` function `v' = s^γ x_{i1}`. -/
noncomputable def sharpV (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    H1Function (euclideanBall (0 : Vec d) 1) :=
  profH1 (sharpW_01 i0 i1) hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1) (sharpW_i1 i0 i1)
    (sharpγ_gt hΛ) (sharpγ_lt hΛ).le

theorem sharpU_toFun (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    (sharpU (d := d) hi hΛ).toFun = prof (sharpW i0 i1) (sharpγ Λ) i0 := rfl

theorem sharpU_grad (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    (sharpU (d := d) hi hΛ).grad = profGrad (sharpW i0 i1) (sharpγ Λ) i0 := rfl

theorem sharpV_toFun (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    (sharpV (d := d) hi hΛ).toFun = prof (sharpW i0 i1) (sharpγ Λ) i1 := rfl

theorem sharpV_grad (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    (sharpV (d := d) hi hΛ).grad = profGrad (sharpW i0 i1) (sharpγ Λ) i1 := rfl

theorem sharp_flux_eq_rot (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) {x : Vec d}
    (hs : 0 < axisSq (sharpW i0 i1) x) :
    matVecMul (meyersCoeff (sharpW i0 i1) Λ x) ((sharpU hi hΛ).grad x) =
      rot i0 i1 (fun j => Real.sqrt Λ * (sharpV hi hΛ).grad x j) := by
  have hq : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
  exact flux_eq_rot hi hq (Real.sq_sqrt (by linarith)).symm rfl hs

/-- The flux `a ∇u` of the planar-type example is in `L²(B₁)`. -/
theorem sharp_flux_memLp (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) (i : Fin d) :
    MemLp (fun x => matVecMul (meyersCoeff (sharpW i0 i1) Λ x) ((sharpU hi hΛ).grad x) i) 2
      (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  refine (memLp_profFlux (sharpW_01 i0 i1) hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1)
    (sharpW_i0 i0 i1) (sharpγ_gt hΛ) (sharpγ_lt hΛ).le Λ i).ae_eq ?_
  filter_upwards [ae_axisSq_pos (sharpW_01 i0 i1) (sharpW_i0 i0 i1)
    (euclideanBall (0 : Vec d) 1)] with x hx
  have := meyersCoeff_matVecMul_profGrad (sharpW_01 i0 i1) hx Λ (sharpγ Λ) (sharpW_i0 i0 i1)
  exact (congrFun this i).symm

/-- **Equation (i).**  `u` is a weak solution of `-div a∇u = 0` in `B₁`. -/
theorem sharp_solution (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    IsWeakDivergenceFormSolutionOn (meyersCoeff (sharpW i0 i1) Λ) (euclideanBall (0 : Vec d) 1)
      (sharpU hi hΛ) (0 : Vec d → ℝ) 0 := by
  refine IsWeakDivergenceFormL2SolutionOn.toIsWeakDivergenceFormSolutionOn
    { flux_memL2 := sharp_flux_memLp hi hΛ
      source_memL2 := MemLp.zero
      forcing_memL2 := fun i => by simp
      identity := ?_ }
  intro φ
  simp only [Pi.zero_apply, zero_mul, integral_zero, vecDot, zero_sub,
    Finset.sum_const_zero, neg_zero, WeakTestFunction.grad_apply]
  have hcurl := curl_pairing (sharpV hi hΛ) i0 i1 (χ := fun _ => (1 : ℝ)) contDiff_const φ
  have h0 : ∀ x : Vec d, fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x = 0 :=
    fun x => (hasFDerivAt_const (1 : ℝ) x).fderiv
  simp only [one_mul, h0, zero_apply, zero_mul, sub_self, mul_zero, integral_zero] at hcurl
  have hae : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
      ∑ j, matVecMul (meyersCoeff (sharpW i0 i1) Λ x) ((sharpU hi hΛ).grad x) j * φ.partialDeriv j x =
        Real.sqrt Λ * ((sharpV hi hΛ).grad x i1 * φ.partialDeriv i0 x -
          (sharpV hi hΛ).grad x i0 * φ.partialDeriv i1 x) := by
    filter_upwards [ae_axisSq_pos (sharpW_01 i0 i1) (sharpW_i0 i0 i1)
      (euclideanBall (0 : Vec d) 1)] with x hx
    have h := sharp_flux_eq_rot hi hΛ hx
    have hd := vecDot_rot hi (fun j => Real.sqrt Λ * (sharpV hi hΛ).grad x j) (φ.grad x)
    rw [← h] at hd
    change vecDot _ _ = _ at hd
    simp only [vecDot, WeakTestFunction.grad_apply] at hd
    rw [hd]; ring
  rw [integral_congr_ae hae, integral_const_mul, hcurl]
  simp

end PDE.Ch4Meyers
