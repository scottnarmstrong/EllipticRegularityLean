module

public import EllipticRegularity.Ch4.Meyers.SharpBounds

/-!
# The planar-type example: the Dirichlet function `U = χ u` and the forcing `f`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {i0 i1 : Fin d}

/-- The cutoff `χ`, equal to one on `B_{1/4}` and supported in `B_{1/2}`. -/
noncomputable def sharpχ : Vec d → ℝ := canonicalBallCutoff (0 : Vec d) (1 / 4) (1 / 2)

theorem sharpχ_smooth : ContDiff ℝ (⊤ : ℕ∞) (sharpχ (d := d)) :=
  canonicalBallCutoff_smooth 0 (by norm_num) (by norm_num)

theorem sharpχ_compact : HasCompactSupport (sharpχ (d := d)) :=
  canonicalBallCutoff_hasCompactSupport (by norm_num) (by norm_num)

theorem sharpχ_tsupport : tsupport (sharpχ (d := d)) ⊆ euclideanBall (0 : Vec d) 1 :=
  (canonicalBallCutoff_tsupport_subset_outer (by norm_num) (by norm_num)).trans
    (euclideanBall_mono (by norm_num) (by norm_num))

theorem sharpχ_one {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 4)) : sharpχ x = 1 :=
  canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num) hx

theorem sharpχ_nonneg (x : Vec d) : 0 ≤ sharpχ x := canonicalBallCutoff_nonneg _ _ _ x

theorem sharpχ_le_one (x : Vec d) : sharpχ x ≤ 1 := canonicalBallCutoff_le_one _ _ _ x

theorem abs_partial_sharpχ_le (x : Vec d) (j : Fin d) :
    |classicalGradient (sharpχ (d := d)) x j| ≤ 128 := by
  have h := canonicalBallCutoff_gradient_bound (d := d) (x₀ := (0 : Vec d)) (r := 1 / 4)
    (R := 1 / 2) (by norm_num) (by norm_num) x
  refine (abs_apply_le_vecEuclideanNorm _ j).trans (h.trans ?_)
  norm_num

theorem measurable_classicalGradient_sharpχ (j : Fin d) :
    Measurable fun x : Vec d => classicalGradient (sharpχ (d := d)) x j := by
  have := (sharpχ_smooth (d := d)).continuous_fderiv (by simp) |>.clm_apply
    (continuous_const (y := basisVec j))
  exact this.measurable

/-- The forcing `f = √Λ v' R∇χ - u a∇χ`. -/
noncomputable def sharpF (i0 i1 : Fin d) (Λ : ℝ) (x : Vec d) : Vec d :=
  (Real.sqrt Λ * prof (sharpW i0 i1) (sharpγ Λ) i1 x) •
      rot i0 i1 (classicalGradient sharpχ x) +
    (-(prof (sharpW i0 i1) (sharpγ Λ) i0 x)) •
      matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (classicalGradient sharpχ x)

theorem measurable_sharpF_apply (i0 i1 : Fin d) (Λ : ℝ) (i : Fin d) :
    Measurable fun x => sharpF i0 i1 Λ x i := by
  unfold sharpF
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact (((measurable_const.mul (measurable_prof _ _ _)).mul
      (measurable_rot_apply measurable_classicalGradient_sharpχ i)).add
    ((measurable_prof _ _ _).neg.mul
      (measurable_matVecMul_meyersCoeff_apply _ _ measurable_classicalGradient_sharpχ i)))

theorem abs_sharpF_apply_le {Λ : ℝ} (hΛ : 1 < Λ) {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) 1) (i : Fin d) :
    |sharpF i0 i1 Λ x i| ≤ Real.sqrt Λ * 128 + d * (Λ * 128) := by
  have hγ0 := sharpγ_gt hΛ
  have hu := abs_prof_le_one (sharpW_01 i0 i1) (sharpW_i0 i0 i1) hγ0 hx
  have hv := abs_prof_le_one (sharpW_01 i0 i1) (sharpW_i1 i0 i1) hγ0 hx
  have hq : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  unfold sharpF
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : |(Real.sqrt Λ * prof (sharpW i0 i1) (sharpγ Λ) i1 x) *
      rot i0 i1 (classicalGradient sharpχ x) i| ≤ Real.sqrt Λ * 128 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hq]
    have := abs_rot_apply_le (i0 := i0) (i1 := i1) (ξ := classicalGradient (sharpχ (d := d)) x)
      (K := 128) (abs_partial_sharpχ_le x) (by norm_num) i
    calc Real.sqrt Λ * |prof (sharpW i0 i1) (sharpγ Λ) i1 x| *
        |rot i0 i1 (classicalGradient sharpχ x) i| ≤ Real.sqrt Λ * 1 * 128 := by gcongr
      _ = _ := by ring
  have h2 : |(-(prof (sharpW i0 i1) (sharpγ Λ) i0 x)) *
      matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (classicalGradient sharpχ x) i| ≤
      d * (Λ * 128) := by
    rw [abs_mul, abs_neg]
    have := abs_matVecMul_le (sharpW_01 i0 i1) hΛ.le x (ξ := classicalGradient (sharpχ (d := d)) x)
      (K := 128) (abs_partial_sharpχ_le x) (by norm_num) i
    calc |prof (sharpW i0 i1) (sharpγ Λ) i0 x| *
        |matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (classicalGradient sharpχ x) i| ≤
        1 * (d * (Λ * 128)) := by gcongr
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem sharpF_bound {Λ : ℝ} (hΛ : 1 < Λ) :
    ∃ M : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) 1, vecEuclideanNorm (sharpF i0 i1 Λ x) ≤ M := by
  refine ⟨d * (Real.sqrt Λ * 128 + d * (Λ * 128)), fun x hx => ?_⟩
  refine (vecEuclideanNorm_le_sum_abs _).trans ?_
  calc ∑ i, |sharpF i0 i1 Λ x i| ≤ ∑ _i : Fin d, (Real.sqrt Λ * 128 + d * (Λ * 128)) :=
        Finset.sum_le_sum fun i _ => abs_sharpF_apply_le hΛ hx i
    _ = _ := by simp; ring

end PDE.Ch4Meyers
