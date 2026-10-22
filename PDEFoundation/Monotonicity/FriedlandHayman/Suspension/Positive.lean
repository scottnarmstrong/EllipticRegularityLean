module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Slice

/-!
# Friedland--Hayman: positivity of the Rayleigh quotient on the circle

For a test function `f` of a proper subdomain `Ω` of the circle `S¹`, the Dirichlet energy
`∫_{S¹} |∇_T f|²` is positive.  Along the way: nonnegativity of the tangential gradient quantity
and the fact that a continuous nonnegative integrand with zero sphere integral vanishes on the sphere.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem tgn_nonneg_of_sphere {n : ℕ} (f : Vec n → ℝ) {x : Vec n}
    (hx : x ∈ euclideanSphere (0 : Vec n) 1) : 0 ≤ tangentialGradientNormSq f x := by
  unfold tangentialGradientNormSq
  have h := sq_vecDot_le_vecNormSq_mul_vecNormSq (classicalGradient f x) x
  rw [mem_euclideanSphere_iff.1 hx, mul_one] at h
  linarith

theorem sphereIntegral_tgn_nonneg {n : ℕ} (f : Vec n → ℝ) :
    0 ≤ sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f) := by
  rw [sphereIntegral_unit]
  exact integral_nonneg fun ω => tgn_nonneg_of_sphere f (toVec_mem_sphere ω)

theorem exists_sphere_toVec {n : ℕ} {x : Vec n} (hx : x ∈ euclideanSphere (0 : Vec n) 1) :
    ∃ ω : Metric.sphere (0 : HilbertVec n) 1, (ω : HilbertVec n).toVec = x := by
  refine ⟨⟨x.toHilbertVec, ?_⟩, rfl⟩
  rw [mem_sphere_zero_iff_norm, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  unfold vecEuclideanNorm
  rw [mem_euclideanSphere_iff.1 hx]
  exact Real.sqrt_one

theorem tgn_eq_zero_of_integral_eq_zero {n : ℕ} {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f)
    (hJ : sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f) = 0) {x : Vec n}
    (hx : x ∈ euclideanSphere (0 : Vec n) 1) : tangentialGradientNormSq f x = 0 := by
  by_contra hne
  obtain ⟨ω0, rfl⟩ := exists_sphere_toVec hx
  have hcont : Continuous fun ω : Metric.sphere (0 : HilbertVec n) 1 =>
      tangentialGradientNormSq f (ω : HilbertVec n).toVec :=
    (continuous_tgn hf).comp (continuous_toVec.comp continuous_subtype_val)
  have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := (volume : Measure (HilbertVec n)).toSphere) (x := ω0)
    (HasCompactSupport.of_compactSpace _)
    (fun ω => tgn_nonneg_of_sphere f (toVec_mem_sphere ω)) hne
  rw [sphereIntegral_unit] at hJ
  exact hpos.ne' hJ

/-- The point `(cos t, sin t)` of the unit circle. -/
def circPt (t : ℝ) : Vec 2 := ![Real.cos t, Real.sin t]

theorem circPt_mem (t : ℝ) : circPt t ∈ euclideanSphere (0 : Vec 2) 1 := by
  rw [mem_euclideanSphere_iff, vecNormSq_eq_sum_sq]
  simp [circPt, Fin.sum_univ_two]

theorem exists_circPt {x : Vec 2} (hx : x ∈ euclideanSphere (0 : Vec 2) 1) : ∃ t, circPt t = x := by
  have h := mem_euclideanSphere_iff.1 hx
  rw [vecNormSq_eq_sum_sq] at h
  simp only [Fin.sum_univ_two] at h
  set z : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I with hz
  have hnorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_add_mul_I, h]; exact Real.sqrt_one
  have hz0 : z ≠ 0 := by intro h0; rw [h0] at hnorm; simp at hnorm
  refine ⟨Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · simp only [circPt, Fin.zero_eta, Matrix.cons_val_zero]
    rw [Complex.cos_arg hz0, hnorm]; simp [hz]
  · simp only [circPt, Fin.mk_one, Matrix.cons_val_one]
    rw [Complex.sin_arg, hnorm]; simp [hz]

theorem hasDerivAt_circPt (t : ℝ) : HasDerivAt circPt ![-Real.sin t, Real.cos t] t := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa [circPt] using Real.hasDerivAt_cos t
  · simpa [circPt] using Real.hasDerivAt_sin t

theorem hasDerivAt_comp_circPt {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    HasDerivAt (fun t => f (circPt t))
      (vecDot (classicalGradient f (circPt t)) ![-Real.sin t, Real.cos t]) t := by
  have h := (hf.differentiable (by simp) (circPt t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_circPt t)
  rw [fderiv_apply_eq_vecDot_classicalGradient] at h
  exact h

theorem deriv_comp_circPt_eq_zero {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) {t : ℝ}
    (h : tangentialGradientNormSq f (circPt t) = 0) :
    deriv (fun t => f (circPt t)) t = 0 := by
  rw [(hasDerivAt_comp_circPt hf t).deriv]
  unfold tangentialGradientNormSq at h
  set p := classicalGradient f (circPt t) with hp
  simp only [vecNormSq_eq_sum_sq, vecDot, Fin.sum_univ_two, circPt] at h ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
  have hsc := Real.sin_sq_add_cos_sq t
  have hd : (-(p 0 * Real.sin t) + p 1 * Real.cos t) ^ 2 = 0 := by
    linear_combination h + (p 0 ^ 2 + p 1 ^ 2) * hsc
  have := pow_eq_zero_iff (two_ne_zero) |>.1 hd
  linarith

/-- On a proper subdomain of the circle every test function has positive Dirichlet energy. -/
theorem sphereIntegral_tgn_pos_circle {Ω : Set (Vec 2)} {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hfΩ : closure {x | x ∈ euclideanSphere (0 : Vec 2) 1 ∧ f x ≠ 0} ⊆ Ω)
    (hI : 0 < sphereIntegral (0 : Vec 2) 1 (fun x => f x ^ 2))
    (hmiss : ∃ p ∈ euclideanSphere (0 : Vec 2) 1, p ∉ Ω) :
    0 < sphereIntegral (0 : Vec 2) 1 (tangentialGradientNormSq f) := by
  refine lt_of_le_of_ne (sphereIntegral_tgn_nonneg f) fun hJ => ?_
  obtain ⟨p, hpS, hpΩ⟩ := hmiss
  have hfp : f p = 0 := by
    by_contra hne
    exact hpΩ (hfΩ (subset_closure ⟨hpS, hne⟩))
  obtain ⟨tp, rfl⟩ := exists_circPt hpS
  have hconst : ∀ t, f (circPt t) = f (circPt tp) := fun t =>
    is_const_of_deriv_eq_zero (f := fun t => f (circPt t))
      (fun t => (hasDerivAt_comp_circPt hf t).differentiableAt)
      (fun t => deriv_comp_circPt_eq_zero hf
        (tgn_eq_zero_of_integral_eq_zero hf hJ.symm (circPt_mem t))) t tp
  have hz : ∀ x ∈ euclideanSphere (0 : Vec 2) 1, f x = 0 := by
    intro x hx
    obtain ⟨t, rfl⟩ := exists_circPt hx
    rw [hconst t, hfp]
  have : sphereIntegral (0 : Vec 2) 1 (fun x => f x ^ 2) = 0 := by
    rw [sphereIntegral_congr_sphere (g := fun _ => 0) (fun x hx => by simp [hz x hx])]
    simp [sphereIntegral]
  linarith

end Susp

end

end PDE.FHLane
