module

public import EllipticRegularity.Ch4.Meyers.Energy

/-!
# Consequence of Proposition 4.7 for the interior Meyers estimate

The theorem `meyers_range_upper_bound_full` has exactly the type of the statement
`meyers_range_upper_bound`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ}

/-- The energy density `√(∇u · a∇u)` of the planar-type example. -/
noncomputable def sharpEnergy (i0 i1 : Fin d) (Λ : ℝ) (x : Vec d) : ℝ :=
  Real.sqrt (vecDot (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x)
    (matVecMul (meyersCoeff (sharpW i0 i1) Λ x) (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x)))

theorem measurable_sharpEnergy (i0 i1 : Fin d) (Λ : ℝ) : Measurable (sharpEnergy i0 i1 Λ) := by
  unfold sharpEnergy
  refine Real.continuous_sqrt.measurable.comp ?_
  simp only [vecDot]
  refine Finset.measurable_sum _ fun i _ => (measurable_profGrad_apply _ _ _ i).mul ?_
  exact measurable_matVecMul_meyersCoeff_apply _ _
    (fun j => measurable_profGrad_apply _ _ _ j) i

theorem vecEuclideanNorm_le_sharpEnergy (i0 i1 : Fin d) {Λ : ℝ} (hΛ : 1 < Λ) (x : Vec d) :
    vecEuclideanNorm (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x) ≤ sharpEnergy i0 i1 Λ x := by
  unfold sharpEnergy vecEuclideanNorm
  apply Real.sqrt_le_sqrt
  have := (isEllipticMatrix_meyersCoeff (sharpW_01 i0 i1) hΛ.le x).coercive
    (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x)
  simpa using this

theorem sharpEnergy_le (i0 i1 : Fin d) {Λ : ℝ} (hΛ : 1 < Λ) {x : Vec d}
    (hs : 0 < axisSq (sharpW i0 i1) x) :
    sharpEnergy i0 i1 Λ x ≤ Real.sqrt Λ * axisSq (sharpW i0 i1) x ^ sharpγ Λ := by
  have hb := (vecEuclideanNorm_profGrad_bounds (sharpW_01 i0 i1) (sharpW_i0 i0 i1)
    (sharpγ_gt hΛ) (sharpγ_lt hΛ).le hs).2
  have h1 := vecDot_matVecMul_meyersCoeff_le (sharpW_01 i0 i1) hΛ.le x
    (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x)
  unfold sharpEnergy
  calc Real.sqrt _ ≤ Real.sqrt (Λ * vecNormSq (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x)) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt Λ * vecEuclideanNorm (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x) := by
        rw [Real.sqrt_mul (by linarith)]; rfl
    _ ≤ Real.sqrt Λ * axisSq (sharpW i0 i1) x ^ sharpγ Λ :=
        mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

theorem memLp_sharpEnergy {i0 i1 : Fin d} (hi : i0 ≠ i1) {Λ : ℝ} (hΛ : 1 < Λ) :
    MemLp (sharpEnergy i0 i1 Λ) 2 (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
  refine memLp_two_of_abs_le_rpow (sharpW_01 i0 i1) hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1)
    (sharpγ_gt hΛ) (sharpγ_lt hΛ).le (measurable_sharpEnergy i0 i1 Λ) (C := Real.sqrt Λ) ?_
  filter_upwards [ae_axisSq_pos (sharpW_01 i0 i1) (sharpW_i0 i0 i1)
    (euclideanBall (0 : Vec d) 1)] with x hx
  have h0 : 0 ≤ sharpEnergy i0 i1 Λ x := Real.sqrt_nonneg _
  rw [abs_of_nonneg h0]
  exact sharpEnergy_le i0 i1 hΛ hx

/-- Consequence of Proposition 4.7 for the interior estimate of Theorem 4.4(i). -/
theorem meyers_range_upper_bound_full (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (h : ∀ Λ : ℝ, 1 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField d,
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ p : ℝ, 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ f : Vec d → Vec d,
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
            (0 : Vec d → ℝ) f →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p)
              (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) ≤
            ENNReal.ofReal C *
              (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
                  (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) +
                euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal p) f)) :
    c ≤ 2
:= by
  by_contra hc2
  push Not at hc2
  -- the choice of `Λ`
  set m : ℝ := c / (c - 2) + 1 with hmdef
  have hc20 : 0 < c - 2 := by linarith
  have hm1 : 1 < m := by
    have : 0 < c / (c - 2) := by positivity
    linarith
  have hm0 : 0 < m := by linarith
  set Λ : ℝ := m ^ 2 with hΛdef
  have hΛ : 1 < Λ := by nlinarith
  have hsq : Real.sqrt Λ = m := Real.sqrt_sq hm0.le
  obtain ⟨C, hCpos, hC⟩ := h Λ hΛ
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have hi : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; simp [hi0, hi1] at this
  set p : ℝ := 2 + c / Real.sqrt Λ with hpdef
  have hp2 : 2 ≤ p := by
    have : 0 ≤ c / Real.sqrt Λ := by positivity
    linarith
  -- `p ≥ p⋆`
  have hpstar : 2 / (1 - 1 / Real.sqrt Λ) ≤ p := by
    rw [hsq]
    have h1 : 0 < 1 - 1 / m := by
      have : 1 / m < 1 := by rw [div_lt_one hm0]; exact hm1
      linarith
    rw [div_le_iff₀ h1]
    have hcm : c / (c - 2) * (c - 2) = c := div_mul_cancel₀ c hc20.ne'
    have key : c ≤ (c - 2) * m := by
      have : (c - 2) * m = c + (c - 2) := by
        rw [hmdef]; nlinarith [hcm]
      linarith
    rw [hpdef, hsq]
    field_simp
    nlinarith
  have hp0 : 0 < p := by linarith
  have hB : volume (euclideanBall (0 : Vec d) 1) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ zero_le_one)
  have hBpos : 0 < volume (euclideanBall (0 : Vec d) 1) := volume_euclideanBall_pos _ one_pos
  have hB2 : volume (euclideanBall (0 : Vec d) (1 / 2)) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hz0 : (fun x : Vec d => vecEuclideanNorm ((0 : Vec d → Vec d) x)) = (0 : Vec d → ℝ) := by
    funext x; simp [vecEuclideanNorm, vecNormSq, vecDot]
  have hmain := hC (meyersCoeff (sharpW i0 i1) Λ)
    (fun i j => (measurable_meyersCoeff_apply _ Λ i j).aemeasurable)
    (fun x _ => isEllipticMatrix_meyersCoeff (sharpW_01 i0 i1) hΛ.le x) p hp2 le_rfl
    (0 : Vec d → Vec d) (fun i => aestronglyMeasurable_const)
    (by rw [hz0]; exact MemLp.zero)
    (sharpU hi hΛ) (sharp_solution hi hΛ)
  -- the right-hand side is finite
  have hE2 : eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2 (sharpEnergy i0 i1 Λ) < ∞ :=
    eLpMeanNormOn_lt_top_of_memLp hBpos hB (memLp_sharpEnergy hi hΛ)
  have hZ : euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p)
      (0 : Vec d → Vec d) = 0 := by
    unfold euclideanFieldELpMeanNormOn eLpMeanNormOn
    rw [hz0]
    exact eLpNorm_zero
  have hrhs : ENNReal.ofReal C * (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
      (sharpEnergy i0 i1 Λ) + euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) (0 : Vec d → Vec d)) < ∞ := by
    rw [hZ, add_zero]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE2
  have hlhs := lt_of_le_of_lt hmain hrhs
  have hen : MemLp (sharpEnergy i0 i1 Λ) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) :=
    memLp_of_eLpMeanNormOn_lt_top hB2 hlhs
  have hgrad : MemLp (fun x => vecEuclideanNorm (profGrad (sharpW i0 i1) (sharpγ Λ) i0 x))
      (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
    refine hen.of_le (measurable_vecEuclideanNorm_profGrad _ _ _).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have h0 : 0 ≤ sharpEnergy i0 i1 Λ x := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _),
      abs_of_nonneg h0]
    exact vecEuclideanNorm_le_sharpEnergy i0 i1 hΛ x
  have := (memLp_gradNorm_iff (sharpW_01 i0 i1) hi (sharpW_i0 i0 i1) (sharpW_i1 i0 i1)
    (fun j h0 h1 => sharpW_rest h0 h1) (sharpγ_gt hΛ) (sharpγ_lt hΛ) (ρ := 1 / 2)
    (by norm_num) hp0).mp hgrad
  rw [mul_neg_sharpγ_lt_one_iff hΛ] at this
  exact absurd hpstar (not_le.mpr this)

end PDE.Ch4Meyers
