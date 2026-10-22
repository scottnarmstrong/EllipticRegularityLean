module

public import PDEFoundation.Monotonicity.Almgren.Shift
public import PDEFoundation.Monotonicity.Almgren.RayScaling
public import PDEFoundation.Monotonicity.Core.FrequencyMonoMonotone
public import PDEFoundation.Monotonicity.Core.Homogeneous
public import PDEFoundation.Monotonicity.Core.Rellich

/-!
# Almgren equality case

Both directions of the equality characterization `N' (r) = 0 ↔ u` is a homogeneous harmonic
polynomial on `B_R`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem euclideanSphere_subset_euclideanBall {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    euclideanSphere (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R := by
  intro x hx
  have h : euclideanSqDist x 0 = r ^ 2 := hx
  show euclideanSqDist x 0 < R ^ 2
  rw [h]
  exact pow_lt_pow_left₀ hrR hr.le two_ne_zero

/-- `(⇒)` of the equality case, in the nondegenerate branch. -/
theorem exists_homogeneous_of_deriv_almgrenFrequency_eq_zero (hd : 0 < d) {u : Vec d → ℝ}
    {R r : ℝ} (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R)
    (hH : ∀ s ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 s (fun x => u x ^ 2))
    (h0 : deriv (almgrenFrequency u) r = 0) :
    ∃ (k : ℕ) (p : MvPolynomial (Fin d) ℝ), p.IsHomogeneous k ∧
      ∀ x ∈ euclideanBall (0 : Vec d) R, u x = MvPolynomial.eval x p := by
  have : NeZero d := ⟨hd.ne'⟩
  have hHr := hH r ⟨hr, hrR⟩
  have hsph := vecDot_gradient_eq_smul_of_deriv_almgrenFrequency_eq_zero hd hu hharm hr hrR
    hHr h0
  have hD := energy_eq_inv_mul_sphereIntegral hd hu hharm hr hrR
  set α := almgrenFrequency u r with hα
  have hlam : sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) /
      sphereIntegral 0 r (fun x => u x ^ 2) = α := by
    rw [hα, almgrenFrequency, hD, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hlam] at hsph
  obtain ⟨hv2, hvharm⟩ := shiftedEuler_harmonic hd hu hharm α
  have hvH : sphereIntegral 0 r
      (fun x => (vecDot x (classicalGradient u x) - α * u x) ^ 2) = 0 := by
    rw [sphereIntegral_zero_congr (g := fun _ => (0 : ℝ))]
    · unfold sphereIntegral; simp
    · intro x hx
      simp only [hsph x hx, sub_self]
      norm_num
  have hv0 := eqOn_zero_of_sphereIntegral_sq_eq_zero hd hv2 hvharm hr hrR hvH
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall 0 R := euclideanBall_mono hr.le hrR.le
  have hutop := contDiffOn_top_of_harmonicOn hd hu hharm
  have hscale : ∀ x ∈ euclideanBall (0 : Vec d) r, ∀ t ∈ Ioc (0 : ℝ) 1,
      u (t • x) = t ^ α * u x := by
    intro x hx t ht
    refine scaling_of_euler_eq (fun y hy => differentiableAt_of_contDiffOn_top
      (isOpen_euclideanBall 0 R) hutop (hsub hy)) (fun y hy => ?_) hx ht
    have := hv0 y hy
    linarith
  have hne : ∃ x ∈ euclideanBall (0 : Vec d) r, u x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hext := eqOn_euclideanBall_of_harmonic_eq_polynomial_inner hd hr hrR.le hu hharm 0
      (fun x hx => by simpa using hcon x hx)
    have hz : sphereIntegral 0 r (fun x => u x ^ 2) = 0 := by
      rw [sphereIntegral_zero_congr (g := fun _ => (0 : ℝ))]
      · unfold sphereIntegral; simp
      · intro x hx
        have := hext (euclideanSphere_subset_euclideanBall hr hrR hx)
        simp only [map_zero] at this
        simp [this]
    exact hHr.ne' hz
  obtain ⟨k, -, p, hp, hup⟩ := exists_isHomogeneous_of_scaling_euclideanBall
    (hutop.mono hsub) hscale hne
  exact ⟨k, p, hp, eqOn_euclideanBall_of_harmonic_eq_polynomial_inner hd hr hrR.le hu hharm p hup⟩

/-- `(⇐)` of the equality case: the frequency of a homogeneous harmonic polynomial is constant. -/
theorem deriv_almgrenFrequency_eq_zero_of_homogeneous (hd : 0 < d) {u : Vec d → ℝ}
    {R r : ℝ} (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : r ∈ Ioo (0 : ℝ) R) {k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k)
    (hup : ∀ x ∈ euclideanBall (0 : Vec d) R, u x = MvPolynomial.eval x p) :
    deriv (almgrenFrequency u) r = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hconst : ∀ s ∈ Ioo (0 : ℝ) R, almgrenFrequency u s =
      if sphereIntegral 0 s (fun x => u x ^ 2) = 0 then 0 else (k : ℝ) := by
    intro s hs
    have hD := energy_eq_inv_mul_sphereIntegral hd hu hharm hs.1 hs.2
    have hgrad : ∀ x ∈ euclideanSphere (0 : Vec d) s,
        u x * vecDot x (classicalGradient u x) = k * u x ^ 2 := by
      intro x hx
      have hxB := euclideanSphere_subset_euclideanBall hs.1 hs.2 hx
      have hev : u =ᶠ[nhds x] fun y => MvPolynomial.eval y p := by
        filter_upwards [(isOpen_euclideanBall (0 : Vec d) R).mem_nhds hxB] with y hy
        exact hup y hy
      have hgr : classicalGradient u x = classicalGradient (fun y => MvPolynomial.eval y p) x := by
        funext i
        simp only [classicalGradient_apply, hev.fderiv_eq]
      rw [hgr, vecDot_classicalGradient_eval_of_isHomogeneous hp, hup x hxB]
      ring
    have hS : sphereIntegral 0 s (fun x => u x * vecDot x (classicalGradient u x)) =
        k * sphereIntegral 0 s (fun x => u x ^ 2) := by
      rw [sphereIntegral_zero_congr (g := fun x => (k : ℝ) * u x ^ 2) hgrad]
      unfold sphereIntegral
      rw [integral_const_mul]
      ring
    unfold almgrenFrequency
    rw [hD, hS]
    by_cases hz : sphereIntegral 0 s (fun x => u x ^ 2) = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte]
      field_simp
      exact mul_div_cancel_left₀ _ hs.1.ne'
  rcases dichotomy_zero_or_sphereIntegral_sq_pos hd hu hharm with hz | hpos
  · have : almgrenFrequency u =ᶠ[nhds r] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
      exact almgrenFrequency_eq_zero_of_eqOn_zero hz hs
    rw [this.deriv_eq]
    simp
  · have : almgrenFrequency u =ᶠ[nhds r] fun _ => (k : ℝ) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
      rw [hconst s hs]
      simp only [(hpos s hs).ne', ↓reduceIte]
    rw [this.deriv_eq]
    simp

end

end PDE
