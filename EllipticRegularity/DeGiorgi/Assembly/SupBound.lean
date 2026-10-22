module

public import EllipticRegularity.DeGiorgi.Assembly.LocalHarnack

/-!
# The local `L^∞` bound (Step 2 of Theorem 4.21)

For `z ∈ B_{3/4}`, both `±u(z + ·/4)` are subsolutions in `B_1`, and Moser's estimate bounds
`ess sup_{B_{1/8}(z)} (±u)` by the `L^p(B_1)` norm of `u`.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

theorem eLpNorm_sign_mul {μ : Measure (Vec d)} {s : ℝ} (hs : s = 1 ∨ s = -1) (f : Vec d → ℝ)
    (p : ℝ≥0∞) : eLpNorm (fun x => s * f x) p μ = eLpNorm f p μ := by
  rcases hs with rfl | rfl
  · simp
  · have : (fun x => (-1 : ℝ) * f x) = -f := by funext x; simp
    rw [this, eLpNorm_neg]

theorem ball_subset_unit_of_mem_three_quarters {x : Vec d}
    (hx : x ∈ euclideanBall (0 : Vec d) (3 / 4)) :
    euclideanBall x (1 / 4) ⊆ euclideanBall (0 : Vec d) 1 := by
  apply euclideanBall_subset_of_center_norm_add_le (by norm_num) (by norm_num)
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  rw [sub_zero] at this ⊢
  linarith

/-- Local `L^∞` bound on `B_{1/8}(z)`, `z ∈ B_{3/4}`, for `±u`. -/
theorem sup_bound_ess (d : ℕ) (hMax : MoserLocalMaxConcl d)
    (hSol : SolAffineTransfer d) :
    ∃ CM : ℝ, 0 < CM ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ p : ℝ, 1 < p → ∀ z ∈ euclideanBall (0 : Vec d) (3 / 4), ∀ s : ℝ, (s = 1 ∨ s = -1) →
        essSup (fun x => ENNReal.ofReal (s * u.toFun x)) (volumeOn (euclideanBall z (1 / 8))) ≤
          ENNReal.ofReal ((4 ^ (d : ℝ) * CM * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) ^
              (1 / p)) *
            eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨CM, hCM, hQM⟩ := hMax
  refine ⟨CM, hCM, ?_⟩
  intro Λ a hmeas hell u hsol p hp z hz s hs
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hsub := ball_subset_unit_of_mem_three_quarters hz
  obtain ⟨ut, hut, hsolt⟩ := hSol Λ a hmeas hell z (1 / 4) hr hsub u hsol s 0
  obtain ⟨hmeast, hellt⟩ := coeff_comp_aff hmeas hell z hr hsub
  have hM := hQM Λ _ hmeast hellt ut (IsSolution.toSub hsolt) p hp
  have hutfun : ut.toFun = fun y => (fun x => s * u.toFun x) (z + (1 / 4 : ℝ) • y) := by
    funext y; rw [hut y]; ring
  have e18 : (1 / 4 : ℝ) * (1 / 2) = 1 / 8 := by norm_num
  have e14 : (1 / 4 : ℝ) * 1 = 1 / 4 := by norm_num
  have hpe : (1 / ENNReal.ofReal p).toReal * p = 1 := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), inv_mul_cancel₀
      (by linarith)]
  have hc : ENNReal.ofReal ((((1 : ℝ) / 4) ^ d)⁻¹) = ENNReal.ofReal ((4 : ℝ) ^ (d : ℝ)) := by
    rw [Real.rpow_natCast, one_div, inv_pow, inv_inv]
  have hpp : 0 < p / (p - 1) := div_pos (by linarith) (by linarith)
  have hN : eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall z (1 / 4))) ≤
      eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
  rw [hutfun, essSup_comp_aff_ball z hr (by norm_num : (0 : ℝ) < 1 / 2)
      (fun x => ENNReal.ofReal (s * u.toFun x)), e18,
    eLpNorm_comp_aff_ball z hr (one_pos : (0 : ℝ) < 1) (ENNReal.ofReal p)
      (fun x => s * u.toFun x), e14, eLpNorm_sign_mul hs,
    ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, hpe, ENNReal.rpow_one, hc]
    at hM
  have hM1 : essSup (fun x => ENNReal.ofReal (s * u.toFun x)) (volumeOn (euclideanBall z (1 / 8))) ^ p ≤
      ENNReal.ofReal (4 ^ (d : ℝ) * CM * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) *
        eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) ^ p := by
    refine hM.trans ?_
    have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos (one_le_of_elliptic hell)
    calc _ ≤ ENNReal.ofReal (CM * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) *
          (ENNReal.ofReal ((4 : ℝ) ^ (d : ℝ)) *
            eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) ^ p) := by
          gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  have hM2 := rpow_root_le (by linarith) hM1
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos (one_le_of_elliptic hell)
  have hnn : 0 ≤ 4 ^ (d : ℝ) * CM * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ) := by positivity
  rwa [ENNReal.ofReal_rpow_of_nonneg hnn (one_div_pos.2 (by linarith)).le] at hM2

end PDE.DGNMAssembly
