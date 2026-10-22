module

public import PDEFoundation.Sobolev.Trace.Model.ExtKernel

/-!
# Derivative profiles of the dilated kernel

For `K(z, t) = t⁻ⁿ ρ(z / t)` the partial derivatives are `t^{-n-1} ψ(z / t)` with the profiles
`extTan n i = ∂ᵢρ` and `extRad n = -(n ρ + w ⬝ ∇ρ)`, which are bounded, continuous, supported in the
closed Euclidean unit ball and have vanishing integral.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Profile of the tangential derivative `∂ᵢ` of the dilated kernel. -/
noncomputable def extTan (n : ℕ) (i : Fin n) (w : Vec n) : ℝ :=
  fderiv ℝ (extKernel n) w (basisVec i)

/-- Profile of the normal derivative `∂ₜ` of the dilated kernel. -/
noncomputable def extRad (n : ℕ) (w : Vec n) : ℝ :=
  -((n : ℝ) * extKernel n w + fderiv ℝ (extKernel n) w w)

theorem continuous_extKernel (n : ℕ) : Continuous (extKernel n) :=
  (extKernel_contDiff n).continuous

theorem continuous_fderiv_extKernel (n : ℕ) : Continuous (fderiv ℝ (extKernel n)) :=
  (extKernel_contDiff n).continuous_fderiv one_ne_zero

theorem hasCompactSupport_fderiv_extKernel (n : ℕ) :
    HasCompactSupport (fderiv ℝ (extKernel n)) :=
  (extKernel_hasCompactSupport n).fderiv (𝕜 := ℝ)

theorem continuous_extRad (n : ℕ) : Continuous (extRad n) := by
  unfold extRad
  have h := continuous_fderiv_extKernel n
  have : Continuous fun w : Vec n => fderiv ℝ (extKernel n) w w :=
    (h.clm_apply continuous_id)
  exact ((continuous_const.mul (continuous_extKernel n)).add this).neg

theorem continuous_extTan (n : ℕ) (i : Fin n) : Continuous (extTan n i) :=
  (continuous_fderiv_extKernel n).clm_apply continuous_const

theorem extRad_eq_zero_of_one_lt (n : ℕ) {w : Vec n} (hw : 1 < vecEuclideanNorm w) :
    extRad n w = 0 := by
  simp [extRad, extKernel_eq_zero_of_one_lt n hw, fderiv_extKernel_eq_zero_of_one_lt n hw]

theorem extTan_eq_zero_of_one_lt (n : ℕ) (i : Fin n) {w : Vec n} (hw : 1 < vecEuclideanNorm w) :
    extTan n i w = 0 := by
  simp [extTan, fderiv_extKernel_eq_zero_of_one_lt n hw]

theorem hasCompactSupport_extRad (n : ℕ) : HasCompactSupport (extRad n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec n) 1) ?_
  intro w hw
  refine extRad_eq_zero_of_one_lt n ?_
  have h := (vecEuclideanNorm_le_sqrt_natCast_mul_norm w)
  by_contra hle
  have hle' : vecEuclideanNorm w ≤ 1 := not_lt.1 hle
  have : ‖w‖ ≤ vecEuclideanNorm w := norm_le_vecEuclideanNorm w
  exact hw (by simpa using this.trans hle')

/-- Uniform bounds for the kernel and its profiles. -/
theorem exists_extKernel_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : Vec n, ‖fderiv ℝ (extKernel n) w‖ ≤ M ∧ |extKernel n w| ≤ M ∧
      |extRad n w| ≤ M := by
  obtain ⟨M1, h1⟩ := (continuous_fderiv_extKernel n).bounded_above_of_compact_support
    (hasCompactSupport_fderiv_extKernel n)
  obtain ⟨M2, h2⟩ := (continuous_extKernel n).bounded_above_of_compact_support
    (extKernel_hasCompactSupport n)
  obtain ⟨M3, h3⟩ := (continuous_extRad n).bounded_above_of_compact_support
    (hasCompactSupport_extRad n)
  refine ⟨max M1 (max M2 M3), le_trans (norm_nonneg _) ((h1 0).trans (le_max_left _ _)), ?_⟩
  intro w
  refine ⟨(h1 w).trans (le_max_left _ _), ?_, ?_⟩
  · have := h2 w
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have := h3 w
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem abs_extTan_le (n : ℕ) (i : Fin n) (w : Vec n) :
    |extTan n i w| ≤ ‖fderiv ℝ (extKernel n) w‖ := by
  have hb : ‖basisVec i‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    by_cases h : j = i <;> simp [basisVec_apply, h]
  have := (fderiv ℝ (extKernel n) w).le_opNorm (basisVec i)
  rw [extTan, ← Real.norm_eq_abs]
  calc _ ≤ ‖fderiv ℝ (extKernel n) w‖ * ‖basisVec i‖ := this
    _ ≤ ‖fderiv ℝ (extKernel n) w‖ * 1 :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_one _

/-- `∫ ∂ᵥ ρ = 0`. -/
theorem integral_fderiv_extKernel (n : ℕ) (v : Vec n) :
    ∫ w, fderiv ℝ (extKernel n) w v = 0 := by
  have hρ : ∀ w, DifferentiableAt ℝ (extKernel n) w :=
    fun w => ((extKernel_contDiff n).differentiable one_ne_zero) w
  have hint : Integrable (fun w => fderiv ℝ (extKernel n) w v) :=
    ((continuous_fderiv_extKernel n).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_extKernel n).comp_left (g := fun L : Vec n →L[ℝ] ℝ => L v)
        (by simp))
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Vec n => (1 : ℝ)) (g := extKernel n) (v := v)
    (by simp)
    (by simpa using hint) (by simpa using extKernel_integrable n)
    (fun _ _ => differentiableAt_const _) (fun w _ => hρ w)
  simpa using this

/-- `∫ wᵢ ∂ᵢρ = -1`. -/
theorem integral_coord_mul_extTan (n : ℕ) (i : Fin n) :
    ∫ w, w i * extTan n i w = -1 := by
  have hρ : ∀ w, DifferentiableAt ℝ (extKernel n) w :=
    fun w => ((extKernel_contDiff n).differentiable one_ne_zero) w
  let c : Vec n →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hc : ∀ w : Vec n, HasFDerivAt (fun w : Vec n => w i) c w := fun w => c.hasFDerivAt
  have hfd : ∀ w : Vec n, fderiv ℝ (fun w : Vec n => w i) w (basisVec i) = 1 := by
    intro w
    rw [(hc w).fderiv]
    simp [c, basisVec]
  have hcont : Continuous fun w : Vec n => w i := continuous_apply i
  have h1 : Integrable (fun w : Vec n => w i * extTan n i w) :=
    ((hcont.mul (continuous_extTan n i)).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_fderiv_extKernel n |>.comp_left
        (g := fun L : Vec n →L[ℝ] ℝ => L (basisVec i)) (by simp))))
  have h2 : Integrable (fun w : Vec n => fderiv ℝ (fun w : Vec n => w i) w (basisVec i) *
      extKernel n w) := by
    simp_rw [hfd, one_mul]; exact extKernel_integrable n
  have h3 : Integrable (fun w : Vec n => w i * extKernel n w) :=
    (hcont.mul (continuous_extKernel n)).integrable_of_hasCompactSupport
      ((extKernel_hasCompactSupport n).mul_left)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun w : Vec n => w i) (g := extKernel n) (v := basisVec i)
    h2 (by simpa [extTan] using h1) h3
    (fun w _ => (hc w).differentiableAt) (fun w _ => hρ w)
  simp_rw [hfd, one_mul] at this
  rw [extKernel_integral] at this
  simpa [extTan] using this

theorem fderiv_extKernel_self_eq_sum (n : ℕ) (w : Vec n) :
    fderiv ℝ (extKernel n) w w = ∑ i : Fin n, w i * extTan n i w := by
  have h : fderiv ℝ (extKernel n) w w = fderiv ℝ (extKernel n) w (∑ i, w i • basisVec i) := by
    rw [sum_smul_basisVec]
  rw [h]
  simp [map_sum, extTan]

theorem integral_extRad (n : ℕ) : ∫ w, extRad n w = 0 := by
  have hcont : ∀ i : Fin n, Continuous fun w : Vec n => w i * extTan n i w := fun i =>
    (continuous_apply i).mul (continuous_extTan n i)
  have hint : ∀ i : Fin n, Integrable (fun w : Vec n => w i * extTan n i w) := fun i =>
    (hcont i).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hasCompactSupport_fderiv_extKernel n |>.comp_left
        (g := fun L : Vec n →L[ℝ] ℝ => L (basisVec i)) (by simp)))
  have h1 : Integrable (fun w : Vec n => fderiv ℝ (extKernel n) w w) := by
    simp_rw [fderiv_extKernel_self_eq_sum]
    exact integrable_finsetSum _ (fun i _ => hint i)
  have h2 : ∫ w : Vec n, fderiv ℝ (extKernel n) w w = -(n : ℝ) := by
    simp_rw [fderiv_extKernel_self_eq_sum]
    rw [integral_finsetSum _ (fun i _ => hint i)]
    simp [integral_coord_mul_extTan]
  unfold extRad
  rw [integral_neg, integral_add ((extKernel_integrable n).const_mul _) h1, h2,
    integral_const_mul, extKernel_integral]
  ring

end PDE.TraceLane
