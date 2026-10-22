module

public import EllipticRegularity.Ch4.Meyers.SharpDirichlet
public import EllipticRegularity.Ch4.Meyers.TestCalculus

/-!
# The planar-type example: `-div a∇U = div f` for `U = χ u`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {i0 i1 : Fin d}

/-- `U = χ u ∈ H¹₀(B₁)`. -/
noncomputable def sharpU10 (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    H10Function (euclideanBall (0 : Vec d) 1) :=
  (sharpU hi hΛ).mulContDiffHasCompactSupportToH10
    (isOpenBoundedConvexDomain_euclideanBall 0 one_pos) sharpχ_smooth sharpχ_compact
    sharpχ_tsupport

theorem sharpU10_toFun (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) (x : Vec d) :
    (sharpU10 hi hΛ).toH1Function.toFun x = sharpχ x * prof (sharpW i0 i1) (sharpγ Λ) i0 x := by
  have := congrFun (H1Function.mulContDiffHasCompactSupportToH10_toFun (sharpU hi hΛ)
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos) sharpχ_smooth
    sharpχ_compact sharpχ_tsupport) x
  exact this

theorem sharpU10_grad (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) (x : Vec d) :
    (sharpU10 hi hΛ).toH1Function.grad x =
      sharpχ x • profGrad (sharpW i0 i1) (sharpγ Λ) i0 x +
        prof (sharpW i0 i1) (sharpγ Λ) i0 x • classicalGradient sharpχ x := by
  have := congrFun (H1Function.mulContDiffHasCompactSupportToH10_grad (sharpU hi hΛ)
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos) sharpχ_smooth
    sharpχ_compact sharpχ_tsupport) x
  exact this

theorem sharp_vecDot_flux (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) {x : Vec d}
    (hs : 0 < axisSq (sharpW i0 i1) x) (η : Vec d) :
    vecDot (matVecMul (meyersCoeff (sharpW i0 i1) Λ x) ((sharpU hi hΛ).grad x)) η =
      Real.sqrt Λ * ((sharpV hi hΛ).grad x i1 * η i0 - (sharpV hi hΛ).grad x i0 * η i1) := by
  rw [sharp_flux_eq_rot hi hΛ hs, vecDot_rot hi]
  ring

theorem sharp_dirichlet_flux_memLp (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) (i : Fin d) :
    MemLp (fun x => matVecMul (meyersCoeff (sharpW i0 i1) Λ x)
      ((sharpU10 hi hΛ).toH1Function.grad x) i) 2
      (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  have hpt : ∀ x, matVecMul (meyersCoeff (sharpW i0 i1) Λ x)
      ((sharpU10 hi hΛ).toH1Function.grad x) i =
      sharpχ x * matVecMul (meyersCoeff (sharpW i0 i1) Λ x) ((sharpU hi hΛ).grad x) i +
        prof (sharpW i0 i1) (sharpγ Λ) i0 x *
          matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (classicalGradient sharpχ x) i := by
    intro x
    rw [sharpU10_grad, sharpU_grad]
    exact matVecMul_comb _ _ _ _ _ _
  simp_rw [hpt]
  refine MemLp.add ?_ ?_
  · refine (sharp_flux_memLp hi hΛ i).of_le_mul (c := 1)
      ((sharpχ_smooth (d := d)).continuous.aestronglyMeasurable.mul
        (sharp_flux_memLp hi hΛ i).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sharpχ_nonneg x), one_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (sharpχ_le_one x)
  · have := isFiniteMeasure_restrict_unitBall (d := d)
    refine MemLp.of_bound ?_ (d * (Λ * 128)) ?_
    · exact ((measurable_prof _ _ _).mul
        (measurable_matVecMul_meyersCoeff_apply _ _ measurable_classicalGradient_sharpχ
          i)).aestronglyMeasurable
    · refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).mpr
        (ae_of_all _ fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_prof_le_one (sharpW_01 i0 i1) (sharpW_i0 i0 i1) (sharpγ_gt hΛ) hx
      have h2 := abs_matVecMul_le (sharpW_01 i0 i1) hΛ.le x
        (ξ := classicalGradient (sharpχ (d := d)) x) (K := 128) (abs_partial_sharpχ_le x)
        (by norm_num) i
      calc _ ≤ 1 * (d * (Λ * 128)) := by gcongr
        _ = _ := by ring

theorem sharp_dirichlet_forcing_memLp (_hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) (i : Fin d) :
    MemLp (fun x => sharpF i0 i1 Λ x i) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  have := isFiniteMeasure_restrict_unitBall (d := d)
  refine MemLp.of_bound (measurable_sharpF_apply i0 i1 Λ i).aestronglyMeasurable
    (Real.sqrt Λ * 128 + d * (Λ * 128)) ?_
  refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).mpr (ae_of_all _ fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_sharpF_apply_le hΛ hx i

/-- **Equation (ii).**  `U = χ u ∈ H¹₀(B₁)` solves `-div a∇U = div f`. -/
theorem sharp_dirichlet_solution (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    IsWeakDivergenceFormSolutionOn (meyersCoeff (sharpW i0 i1) Λ) (euclideanBall (0 : Vec d) 1)
      (sharpU10 hi hΛ).toH1Function (0 : Vec d → ℝ) (sharpF i0 i1 Λ) := by
  have hdata : DivergenceFormL2DataOn (meyersCoeff (sharpW i0 i1) Λ) (euclideanBall (0 : Vec d) 1)
      (sharpU10 hi hΛ).toH1Function (0 : Vec d → ℝ) (sharpF i0 i1 Λ) :=
    { flux_memL2 := sharp_dirichlet_flux_memLp hi hΛ
      source_memL2 := MemLp.zero
      forcing_memL2 := sharp_dirichlet_forcing_memLp hi hΛ }
  refine IsWeakDivergenceFormL2SolutionOn.toIsWeakDivergenceFormSolutionOn
    { toDivergenceFormL2DataOn := hdata, identity := ?_ }
  intro ψ
  obtain ⟨hA, -, hB⟩ := hdata.testable ψ
  have hsum : (∫ x in euclideanBall (0 : Vec d) 1,
        vecDot (matVecMul (meyersCoeff (sharpW i0 i1) Λ x)
          ((sharpU10 hi hΛ).toH1Function.grad x)) (ψ.grad x)) +
      (∫ x in euclideanBall (0 : Vec d) 1, vecDot (sharpF i0 i1 Λ x) (ψ.grad x)) = 0 := by
    rw [← integral_add hA hB]
    have hzero := curl_pairing_zero (sharpV hi hΛ) i0 i1 (χ := sharpχ) sharpχ_smooth ψ
    have hae : ∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) 1)),
        vecDot (matVecMul (meyersCoeff (sharpW i0 i1) Λ x)
          ((sharpU10 hi hΛ).toH1Function.grad x)) (ψ.grad x) +
        vecDot (sharpF i0 i1 Λ x) (ψ.grad x) =
        Real.sqrt Λ * ((sharpV hi hΛ).grad x i1 * (sharpχ x * ψ.partialDeriv i0 x) -
          (sharpV hi hΛ).grad x i0 * (sharpχ x * ψ.partialDeriv i1 x) +
          (sharpV hi hΛ).toFun x * (fderiv ℝ sharpχ x (basisVec i1) * ψ.partialDeriv i0 x -
            fderiv ℝ sharpχ x (basisVec i0) * ψ.partialDeriv i1 x)) := by
      filter_upwards [ae_axisSq_pos (sharpW_01 i0 i1) (sharpW_i0 i0 i1)
        (euclideanBall (0 : Vec d) 1)] with x hx
      have e1 : matVecMul (meyersCoeff (sharpW i0 i1) Λ x)
          ((sharpU10 hi hΛ).toH1Function.grad x) =
          sharpχ x • matVecMul (meyersCoeff (sharpW i0 i1) Λ x) ((sharpU hi hΛ).grad x) +
            prof (sharpW i0 i1) (sharpγ Λ) i0 x •
              matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (classicalGradient sharpχ x) := by
        funext i
        rw [sharpU10_grad, sharpU_grad]
        exact matVecMul_comb _ _ _ _ _ i
      rw [e1, vecDot_comb]
      unfold sharpF
      rw [vecDot_comb, sharp_vecDot_flux hi hΛ hx, vecDot_rot hi]
      have hc : ∀ j, classicalGradient (sharpχ (d := d)) x j = fderiv ℝ sharpχ x (basisVec j) :=
        fun j => rfl
      simp only [WeakTestFunction.grad_apply, hc]
      change _ = _
      have hv : (sharpV hi hΛ).toFun x = prof (sharpW i0 i1) (sharpγ Λ) i1 x := rfl
      rw [hv]
      ring
    rw [integral_congr_ae hae, integral_const_mul, hzero, mul_zero]
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  linarith

end PDE.Ch4Meyers
