module

public import PDEFoundation.Analysis.Newtonian.Potential.Smooth

/-!
# Integrability and decay of the Newton potential

* `integrable_vecDot_newtonKernel_sub`: the integrand defining `newtonPotential F x` is integrable.
* `abs_newtonPotential_le`: `|u_F x| ≤ C |x|^{1-d}` for `|x| ≥ 2R` when `tsupport F ⊆ B_R`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The integrand of the Newton potential is integrable for every `x`. -/
theorem integrable_vecDot_newtonKernel_sub (hd : 0 < d) {F : Vec d → Vec d}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Vec d) :
    Integrable (fun y => vecDot (newtonKernel (x - y)) (F y)) volume := by
  unfold vecDot
  refine integrable_finsetSum _ fun i _ => ?_
  have h := (hasCompactSupport_apply hFc i).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_newtonKernel_apply hd i)
      ((continuous_apply i).comp hF) x
  exact (ConvolutionExistsAt.integrable_swap h)

/-- The Euclidean norm of a compactly supported continuous field is integrable. -/
theorem integrable_vecEuclideanNorm_comp {F : Vec d → Vec d}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable (fun y => vecEuclideanNorm (F y)) volume := by
  refine Continuous.integrable_of_hasCompactSupport
    (continuous_vecEuclideanNorm.comp hF) ?_
  exact hFc.comp_left (g := fun v : Vec d => vecEuclideanNorm v)
    (by simp [vecEuclideanNorm, vecNormSq, vecDot])

theorem vecEuclideanNorm_lt_of_ne_zero {F : Vec d → Vec d} {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport F ⊆ euclideanBall 0 R) {y : Vec d} (hy : F y ≠ 0) :
    vecEuclideanNorm y < R := by
  have hmem : y ∈ euclideanBall (0 : Vec d) R :=
    hsupp (subset_tsupport F (Function.mem_support.mpr hy))
  have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hmem
  simpa only [sub_zero] using this

theorem half_rpow_eq {a : ℝ} (ha : 0 ≤ a) (e : ℝ) :
    (a / 2) ^ e = (2 : ℝ) ^ (-e) * a ^ e := by
  rw [div_eq_mul_inv, Real.mul_rpow ha (by norm_num), Real.inv_rpow (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  ring

/-- Decay of the Newton potential: `|u_F x| ≤ C |x|^{1-d}` for `|x| ≥ 2R`. -/
theorem abs_newtonPotential_le (hd : 0 < d) {F : Vec d → Vec d}
    (hF : Continuous F) (hFc : HasCompactSupport F) {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport F ⊆ euclideanBall 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, 2 * R ≤ vecEuclideanNorm x →
      |newtonPotential F x| ≤ C * vecEuclideanNorm x ^ ((1 : ℝ) - d) := by
  have hI := integrable_vecEuclideanNorm_comp hF hFc
  refine ⟨newtonConst d * (2 : ℝ) ^ ((d : ℝ) - 1) * ∫ y, vecEuclideanNorm (F y), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg newtonConst_nonneg (Real.rpow_nonneg (by norm_num) _))
      (integral_nonneg fun y => vecEuclideanNorm_nonneg _)
  intro x hx
  have hxpos : 0 < vecEuclideanNorm x := by linarith
  have hxh : 0 < vecEuclideanNorm x / 2 := by linarith
  have hd1 : (1 : ℝ) - d ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set c' : ℝ := newtonConst d * (vecEuclideanNorm x / 2) ^ ((1 : ℝ) - d) with hc'
  have hc'nn : 0 ≤ c' := mul_nonneg newtonConst_nonneg (Real.rpow_nonneg hxh.le _)
  have hpt : ∀ y : Vec d, ‖vecDot (newtonKernel (x - y)) (F y)‖ ≤
      c' * vecEuclideanNorm (F y) := by
    intro y
    rw [Real.norm_eq_abs]
    by_cases hy : F y = 0
    · have : vecDot (newtonKernel (x - y)) (F y) = 0 := by simp [hy, vecDot]
      rw [this, abs_zero]
      exact mul_nonneg hc'nn (vecEuclideanNorm_nonneg _)
    · have hyR := vecEuclideanNorm_lt_of_ne_zero hR hsupp hy
      have hxy : vecEuclideanNorm x / 2 ≤ vecEuclideanNorm (x - y) := by
        have h1 := vecEuclideanNorm_add_le (x - y) y
        rw [sub_add_cancel] at h1
        linarith
      calc |vecDot (newtonKernel (x - y)) (F y)|
          ≤ vecEuclideanNorm (newtonKernel (x - y)) * vecEuclideanNorm (F y) :=
            abs_vecDot_le_vecEuclideanNorm_mul _ _
        _ ≤ c' * vecEuclideanNorm (F y) := by
            refine mul_le_mul_of_nonneg_right ?_ (vecEuclideanNorm_nonneg _)
            refine (vecEuclideanNorm_newtonKernel_le _).trans ?_
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hxh hxy hd1) newtonConst_nonneg
  have hint : Integrable (fun y => c' * vecEuclideanNorm (F y)) volume := hI.const_mul c'
  have hbound := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hbound
  have hu : newtonPotential F x = ∫ y, vecDot (newtonKernel (x - y)) (F y) := rfl
  rw [hu]
  refine (Real.norm_eq_abs _ ▸ hbound).trans ?_
  rw [hc', half_rpow_eq hxpos.le, neg_sub]
  apply le_of_eq
  ring

end

end PDE
