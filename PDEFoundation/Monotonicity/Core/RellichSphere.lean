module

public import PDEFoundation.Monotonicity.Core.BallDivergence
public import PDEFoundation.Monotonicity.Core.Bridge

/-!
# Spheres: parametrization, congruence, linearity, Cauchy-Schwarz

Facts about the `PDE.sphereIntegral` about `0`: it only depends on the integrand on
`euclideanSphere 0 r`, it is linear on functions continuous on the sphere, and the Cauchy-Schwarz
inequality with its equality case holds (the surface measure has full support).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-! ### Abstract Cauchy-Schwarz on a measure space -/

section Abstract

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}

theorem integrable_sq_sub_smul (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) (t : ℝ) :
    Integrable (fun x => (g x - t * f x) ^ 2) μ := by
  have h : ∀ x, (g x - t * f x) ^ 2 = g x ^ 2 - (2 * t) * (f x * g x) + t ^ 2 * f x ^ 2 := by
    intro x; ring
  simp_rw [h]
  exact (hg.sub (hfg.const_mul _)).add (hf.const_mul _)

theorem integral_sq_sub_smul (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) (t : ℝ) :
    ∫ x, (g x - t * f x) ^ 2 ∂μ =
      ∫ x, g x ^ 2 ∂μ - 2 * t * ∫ x, f x * g x ∂μ + t ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  have h : ∀ x, (g x - t * f x) ^ 2 = g x ^ 2 - (2 * t) * (f x * g x) + t ^ 2 * f x ^ 2 := by
    intro x; ring
  simp_rw [h]
  have i1 : Integrable (fun x => g x ^ 2 - (2 * t) * (f x * g x)) μ :=
    hg.sub (hfg.const_mul _)
  have i2 : Integrable (fun x => t ^ 2 * f x ^ 2) μ := hf.const_mul _
  rw [integral_add i1 i2, integral_sub hg (hfg.const_mul _), integral_const_mul,
    integral_const_mul]

/-- Cauchy-Schwarz for square-integrable functions. -/
theorem integral_mul_sq_le (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hnn : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, f x * g x ∂μ) * t +
      ∫ x, g x ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ x, (g x - t * f x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    rw [integral_sq_sub_smul hf hg hfg] at h0
    linarith only [h0]
  have := discrim_le_zero hnn
  unfold discrim at this
  nlinarith only [this]

/-- Equality case of Cauchy-Schwarz: `g = λ f` almost everywhere. -/
theorem ae_eq_smul_of_integral_mul_sq_eq (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hfg : Integrable (fun x => f x * g x) μ)
    (hA : 0 < ∫ x, f x ^ 2 ∂μ)
    (heq : (∫ x, f x * g x ∂μ) ^ 2 = (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ) :
    ∀ᵐ x ∂μ, g x = ((∫ x, f x * g x ∂μ) / ∫ x, f x ^ 2 ∂μ) * f x := by
  set A := ∫ x, f x ^ 2 ∂μ
  set B := ∫ x, f x * g x ∂μ
  set C := ∫ x, g x ^ 2 ∂μ
  have h0 : ∫ x, (g x - (B / A) * f x) ^ 2 ∂μ = 0 := by
    rw [integral_sq_sub_smul hf hg hfg]
    change C - 2 * (B / A) * B + (B / A) ^ 2 * A = 0
    field_simp
    linarith only [heq]
  have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (integrable_sq_sub_smul hf hg hfg (B / A))).1 h0
  filter_upwards [h1] with x hx
  have : (g x - B / A * f x) ^ 2 = 0 := hx
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith only [this]

end Abstract

/-! ### Sphere parametrization -/

theorem mem_euclideanSphere_zero_iff {x : Vec d} {r : ℝ} :
    x ∈ euclideanSphere (0 : Vec d) r ↔ vecNormSq x = r ^ 2 := by
  unfold euclideanSphere
  simp only [mem_ofPred_eq, BallDivergence.euclideanSqDist_zero_right]

theorem sphere_smul_toVec_mem (r : ℝ) (ω : Metric.sphere (0 : HilbertVec d) 1) :
    r • (ω : HilbertVec d).toVec ∈ euclideanSphere (0 : Vec d) r := by
  rw [mem_euclideanSphere_zero_iff, vecNormSq_smul, BallDivergence.vecNormSq_toVec,
    mem_sphere_zero_iff_norm.1 ω.2]
  ring

theorem exists_sphere_smul_toVec_eq {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : x ∈ euclideanSphere (0 : Vec d) r) :
    ∃ ω : Metric.sphere (0 : HilbertVec d) 1, r • (ω : HilbertVec d).toVec = x := by
  rw [mem_euclideanSphere_zero_iff] at hx
  have hn : ‖(r⁻¹ • x).toHilbertVec‖ = 1 := by
    rw [← Vec.vecEuclideanNorm_eq_norm_toHilbertVec, vecEuclideanNorm, vecNormSq_smul, hx]
    rw [show r⁻¹ ^ 2 * r ^ 2 = 1 by field_simp]
    simp
  refine ⟨⟨(r⁻¹ • x).toHilbertVec, mem_sphere_zero_iff_norm.2 hn⟩, ?_⟩
  show r • (r⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem continuous_sphere_smul_toVec (r : ℝ) :
    Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 => r • (ω : HilbertVec d).toVec) :=
  (BallDivergence.continuous_toVec.comp continuous_subtype_val).const_smul r

theorem sphereIntegral_zero_apply (r : ℝ) (f : Vec d → ℝ) :
    sphereIntegral (0 : Vec d) r f = r ^ (d - 1) *
      ∫ ω : Metric.sphere (0 : HilbertVec d) 1, f (r • (ω : HilbertVec d).toVec)
        ∂((volume : Measure (HilbertVec d)).toSphere) := by
  simp only [sphereIntegral, zero_add]

theorem sphereIntegral_zero_congr {r : ℝ} {f g : Vec d → ℝ}
    (h : EqOn f g (euclideanSphere (0 : Vec d) r)) :
    sphereIntegral (0 : Vec d) r f = sphereIntegral (0 : Vec d) r g := by
  rw [sphereIntegral_zero_apply, sphereIntegral_zero_apply]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact h (sphere_smul_toVec_mem r ω)

theorem integrable_sphere_comp {r : ℝ} {f : Vec d → ℝ}
    (hf : ContinuousOn f (euclideanSphere (0 : Vec d) r)) :
    Integrable (fun ω : Metric.sphere (0 : HilbertVec d) 1 => f (r • (ω : HilbertVec d).toVec))
      ((volume : Measure (HilbertVec d)).toSphere) := by
  have hc : Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      f (r • (ω : HilbertVec d).toVec)) :=
    hf.comp_continuous (continuous_sphere_smul_toVec r) (sphere_smul_toVec_mem r)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Linearity of the sphere integral for functions continuous on the sphere. -/
theorem sphereIntegral_zero_sub_const_mul {r a b : ℝ} {f g : Vec d → ℝ}
    (hf : ContinuousOn f (euclideanSphere (0 : Vec d) r))
    (hg : ContinuousOn g (euclideanSphere (0 : Vec d) r)) :
    sphereIntegral (0 : Vec d) r (fun x => a * f x - b * g x) =
      a * sphereIntegral (0 : Vec d) r f - b * sphereIntegral (0 : Vec d) r g := by
  simp only [sphereIntegral_zero_apply]
  rw [integral_sub ((integrable_sphere_comp hf).const_mul a)
    ((integrable_sphere_comp hg).const_mul b), integral_const_mul, integral_const_mul]
  ring

/-! ### Cauchy-Schwarz on the sphere -/

theorem sphereIntegral_zero_mul_sq_le {r : ℝ} {f g : Vec d → ℝ}
    (hf : ContinuousOn f (euclideanSphere (0 : Vec d) r))
    (hg : ContinuousOn g (euclideanSphere (0 : Vec d) r)) :
    sphereIntegral (0 : Vec d) r (fun x => f x * g x) ^ 2 ≤
      sphereIntegral (0 : Vec d) r (fun x => f x ^ 2) *
        sphereIntegral (0 : Vec d) r (fun x => g x ^ 2) := by
  simp only [sphereIntegral_zero_apply]
  have := integral_mul_sq_le (μ := (volume : Measure (HilbertVec d)).toSphere)
    (integrable_sphere_comp (hf.pow 2)) (integrable_sphere_comp (hg.pow 2))
    (integrable_sphere_comp (hf.mul hg))
  nlinarith only [this, sq_nonneg (r ^ (d - 1))]

/-- Equality case of Cauchy-Schwarz on the sphere: if equality holds and `∫ f² > 0`, then
`g = λ f` at every point of the sphere, with `λ = ∫ f g / ∫ f²`.  (Continuity and the full support
of the surface measure upgrade the almost-everywhere statement.) -/
theorem sphereIntegral_zero_eq_smul_of_mul_sq_eq {r : ℝ} (hr : 0 < r) {f g : Vec d → ℝ}
    (hf : ContinuousOn f (euclideanSphere (0 : Vec d) r))
    (hg : ContinuousOn g (euclideanSphere (0 : Vec d) r))
    (hA : 0 < sphereIntegral (0 : Vec d) r (fun x => f x ^ 2))
    (heq : sphereIntegral (0 : Vec d) r (fun x => f x * g x) ^ 2 =
      sphereIntegral (0 : Vec d) r (fun x => f x ^ 2) *
        sphereIntegral (0 : Vec d) r (fun x => g x ^ 2)) :
    ∀ x ∈ euclideanSphere (0 : Vec d) r,
      g x = (sphereIntegral (0 : Vec d) r (fun x => f x * g x) /
        sphereIntegral (0 : Vec d) r (fun x => f x ^ 2)) * f x := by
  have hc : 0 < r ^ (d - 1) := pow_pos hr _
  simp only [sphereIntegral_zero_apply] at hA heq ⊢
  set μ := (volume : Measure (HilbertVec d)).toSphere
  set c := r ^ (d - 1)
  have hA' : 0 < ∫ ω, f (r • (ω : HilbertVec d).toVec) ^ 2 ∂μ := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith only [hA, hneg, hc]
  have heq' : (∫ ω, f (r • (ω : HilbertVec d).toVec) * g (r • (ω : HilbertVec d).toVec) ∂μ) ^ 2 =
      (∫ ω, f (r • (ω : HilbertVec d).toVec) ^ 2 ∂μ) *
        ∫ ω, g (r • (ω : HilbertVec d).toVec) ^ 2 ∂μ := by
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
    apply mul_left_cancel₀ hc2
    linear_combination heq
  have hae := ae_eq_smul_of_integral_mul_sq_eq (μ := μ)
    (f := fun ω : Metric.sphere (0 : HilbertVec d) 1 => f (r • (ω : HilbertVec d).toVec))
    (g := fun ω : Metric.sphere (0 : HilbertVec d) 1 => g (r • (ω : HilbertVec d).toVec))
    (integrable_sphere_comp (hf.pow 2)) (integrable_sphere_comp (hg.pow 2))
    (integrable_sphere_comp (hf.mul hg)) hA' heq'
  have hcf : Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      f (r • (ω : HilbertVec d).toVec)) :=
    hf.comp_continuous (continuous_sphere_smul_toVec r) (sphere_smul_toVec_mem r)
  have hcg : Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      g (r • (ω : HilbertVec d).toVec)) :=
    hg.comp_continuous (continuous_sphere_smul_toVec r) (sphere_smul_toVec_mem r)
  have hall := (Continuous.ae_eq_iff_eq μ hcg (continuous_const.mul hcf)).1 hae
  intro x hx
  obtain ⟨ω, rfl⟩ := exists_sphere_smul_toVec_eq hr hx
  have h1 := congrFun hall ω
  simp only [Pi.mul_apply] at h1
  rw [h1]
  have hcne : c ≠ 0 := hc.ne'
  field_simp

end

end PDE
