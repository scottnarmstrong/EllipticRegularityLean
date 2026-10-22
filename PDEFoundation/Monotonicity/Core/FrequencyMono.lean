module

public import PDEFoundation.Monotonicity.Core.FrequencyDerivs
public import PDEFoundation.Monotonicity.Core.Rellich
public import PDEFoundation.Monotonicity.Core.Bridge
public import PDEFoundation.Monotonicity.Defs

/-!
# Chapter 2: the derivative of the Almgren frequency

For `u` of class `C²` and harmonic on `B_R ⊆ ℝᵈ` (`d ≥ 1`), write `H(r) = ∫_{∂B_r} u²`,
`P(r) = ∫_{∂B_r} u (x · ∇u)` and `Q(r) = ∫_{∂B_r} (x · ∇u)²`. On `(0, R)` where `H > 0` the
frequency `N = r D / H` is differentiable with `N' = 2 (Q H - P²) / (r H²) ≥ 0`
(Cauchy-Schwarz on the sphere), and `N' = 0` forces `x · ∇u = λ u` on `∂B_r`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

/-- `H' = (d - 1) / r * H + 2 D`. -/
theorem hasDerivAt_sphereIntegral_sq (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    HasDerivAt (fun s => sphereIntegral 0 s (fun x => u x ^ 2))
      (((d : ℝ) - 1) / r * sphereIntegral 0 r (fun x => u x ^ 2) +
        2 * ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x)) r := by
  have : NeZero d := ⟨hd.ne'⟩
  have hm := hasDerivAt_sphereMean_sq hd hu hharm hr hrR
  have hp : HasDerivAt (fun s : ℝ => s ^ (d - 1)) (((d - 1 : ℕ) : ℝ) * r ^ (d - 1 - 1)) r :=
    hasDerivAt_pow (d - 1) r
  have h := (hp.const_mul (sphereArea d)).mul hm
  have hfun : (fun s => sphereIntegral 0 s (fun x => u x ^ 2)) =
      fun s => sphereArea d * s ^ (d - 1) * sphereMean 0 s (fun x => u x ^ 2) :=
    funext fun s => sphereIntegral_eq_mul_sphereMean _ _ _
  rw [hfun]
  refine h.congr_deriv ?_
  have hσ := sphereArea_pos (d := d)
  rw [sphereIntegral_eq_mul_sphereMean]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have hrk : r ^ k ≠ 0 := pow_ne_zero _ hr.ne'
  have hkr : (k : ℝ) * r ^ (k - 1) = k / r * r ^ k := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
  set A := sphereArea (k + 1)
  rw [hkr]
  field_simp

/-- Pure algebra of the frequency derivative. -/
theorem frequency_deriv_algebra {r D E Q P H n : ℝ} (hr : r ≠ 0) (hH : H ≠ 0)
    (hP : D = r⁻¹ * P) (hRel : (n - 2) * D = r * E - 2 * r⁻¹ * Q) :
    ((1 * D + r * E) * H - r * D * ((n - 1) / r * H + 2 * D)) / H ^ 2 =
      2 * (Q * H - P ^ 2) / (r * H ^ 2) := by
  have hE : E = ((n - 2) * D + 2 * r⁻¹ * Q) / r := by
    rw [eq_div_iff hr]
    linear_combination (-1 : ℝ) * hRel
  subst hE
  subst hP
  field_simp
  ring

/-- The derivative of the Almgren frequency on `{H > 0}`: `N' = 2 (Q H - P²) / (r H²)`. -/
theorem hasDerivAt_almgrenFrequency_of_pos (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) (hH : 0 < sphereIntegral 0 r (fun x => u x ^ 2)) :
    HasDerivAt (almgrenFrequency u)
      (2 * (sphereIntegral 0 r (fun x => vecDot x (classicalGradient u x) ^ 2) *
          sphereIntegral 0 r (fun x => u x ^ 2) -
          sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) ^ 2) /
        (r * sphereIntegral 0 r (fun x => u x ^ 2) ^ 2)) r := by
  have hD := hasDerivAt_energy hd hu hharm hr hrR
  have hHd := hasDerivAt_sphereIntegral_sq hd hu hharm hr hrR
  have hnum := (hasDerivAt_id r).mul hD
  have h := hnum.div hHd hH.ne'
  have hfun : almgrenFrequency u = fun s => (id s * ∫ x in euclideanBall (0 : Vec d) s,
      vecNormSq (classicalGradient u x)) / sphereIntegral 0 s (fun x => u x ^ 2) := by
    funext s; rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hP := energy_eq_inv_mul_sphereIntegral hd hu hharm hr hrR
  have hRel := rellich_identity hd hu hharm hr hrR
  have := frequency_deriv_algebra (n := (d : ℝ)) hr.ne' hH.ne' hP hRel
  simpa using this

/-- `deriv N = 2 (Q H - P²) / (r H²)` on `{H > 0}`. -/
theorem deriv_almgrenFrequency_eq_of_pos (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) (hH : 0 < sphereIntegral 0 r (fun x => u x ^ 2)) :
    deriv (almgrenFrequency u) r =
      2 * (sphereIntegral 0 r (fun x => vecDot x (classicalGradient u x) ^ 2) *
          sphereIntegral 0 r (fun x => u x ^ 2) -
          sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) ^ 2) /
        (r * sphereIntegral 0 r (fun x => u x ^ 2) ^ 2) :=
  (hasDerivAt_almgrenFrequency_of_pos hd hu hharm hr hrR hH).deriv

/-- `N' ≥ 0` on `{H > 0}`, by Cauchy-Schwarz on the sphere. -/
theorem deriv_almgrenFrequency_nonneg (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) (hH : 0 < sphereIntegral 0 r (fun x => u x ^ 2)) :
    0 ≤ deriv (almgrenFrequency u) r := by
  rw [(hasDerivAt_almgrenFrequency_of_pos hd hu hharm hr hrR hH).deriv]
  have htop := contDiffOn_top_of_harmonicOn hd hu hharm
  have hsph : euclideanSphere (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R := by
    intro x hx
    rw [mem_euclideanSphere_zero_iff] at hx
    rw [mem_euclideanBall_zero_iff, hx]
    nlinarith only [hr, hrR]
  have hf := hu.continuousOn.mono hsph
  have hg := (contDiffOn_euler (isOpen_euclideanBall 0 R) htop).continuousOn.mono hsph
  have hcs := sphereIntegral_zero_mul_sq_le hf hg
  have : 0 ≤ sphereIntegral 0 r (fun x => vecDot x (classicalGradient u x) ^ 2) *
      sphereIntegral 0 r (fun x => u x ^ 2) -
      sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) ^ 2 := by
    linarith only [hcs, mul_comm (sphereIntegral 0 r (fun x => u x ^ 2))
      (sphereIntegral 0 r (fun x => vecDot x (classicalGradient u x) ^ 2))]
  positivity

/-- Equality case: `N' (r) = 0` with `H(r) > 0` forces `x · ∇u = λ u` on `∂B_r`. -/
theorem vecDot_gradient_eq_smul_of_deriv_almgrenFrequency_eq_zero (hd : 0 < d) {u : Vec d → ℝ}
    {R r : ℝ} (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) (hH : 0 < sphereIntegral 0 r (fun x => u x ^ 2))
    (h0 : deriv (almgrenFrequency u) r = 0) :
    ∀ x ∈ euclideanSphere (0 : Vec d) r,
      vecDot x (classicalGradient u x) =
        (sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) /
          sphereIntegral 0 r (fun x => u x ^ 2)) * u x := by
  rw [(hasDerivAt_almgrenFrequency_of_pos hd hu hharm hr hrR hH).deriv] at h0
  have htop := contDiffOn_top_of_harmonicOn hd hu hharm
  have hsph : euclideanSphere (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R := by
    intro x hx
    rw [mem_euclideanSphere_zero_iff] at hx
    rw [mem_euclideanBall_zero_iff, hx]
    nlinarith only [hr, hrR]
  have hf := hu.continuousOn.mono hsph
  have hg := (contDiffOn_euler (isOpen_euclideanBall 0 R) htop).continuousOn.mono hsph
  refine sphereIntegral_zero_eq_smul_of_mul_sq_eq hr hf hg hH ?_
  have hr' : r * sphereIntegral 0 r (fun x => u x ^ 2) ^ 2 ≠ 0 := by positivity
  have h1 := (div_eq_zero_iff.mp h0).resolve_right hr'
  have h2 : sphereIntegral 0 r (fun x => vecDot x (classicalGradient u x) ^ 2) *
      sphereIntegral 0 r (fun x => u x ^ 2) -
      sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) ^ 2 = 0 := by
    linarith only [h1]
  linarith only [h2, mul_comm (sphereIntegral 0 r (fun x => u x ^ 2))
      (sphereIntegral 0 r (fun x => vecDot x (classicalGradient u x) ^ 2))]

end

end PDE
