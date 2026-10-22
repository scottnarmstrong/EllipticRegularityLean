module

public import PDEFoundation.Monotonicity.Core.FrequencyDerivsLocal
public import PDEFoundation.Monotonicity.Core.FrequencyDerivsGlobal
public import PDEFoundation.Monotonicity.Core.FrequencyDerivsOneAffine
public import PDEFoundation.Monotonicity.Core.HarmonicFacade

/-!
# Chapter 2: radial derivatives of the Almgren quantities

For `u` of class `C²` and harmonic on the ball `B_R ⊆ ℝᵈ` (`d ≥ 1`), with
`H(r) = ∫_{∂B_r} u²` and `D(r) = ∫_{B_r} |∇u|²` (the data of `almgrenFrequency`):

* `D(r) = r⁻¹ ∫_{∂B_r} u (x · ∇u)`;
* `r ↦ ⨍_{∂B_r} u²` has derivative `2 D(r) / (σ_d r^{d-1})`;
* `D' (r) = ∫_{∂B_r} |∇u|²`, and `D`, `H` are continuous on `(0, R)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Localization of a `C²` harmonic function on a ball to a globally smooth harmonic one. -/
theorem exists_harmonic_localization (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ} (hr : 0 < r)
    (hrR : r < R) (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ∃ (ρ' : ℝ) (v : Vec d → ℝ), r < ρ' ∧ ρ' < R ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧
      EqOn v u (euclideanBall 0 ρ') ∧
      ∀ y ∈ euclideanBall (0 : Vec d) ρ', euclideanCoordLaplacian v y = 0 := by
  obtain ⟨ρ', v, h1, h2, hv, hvu⟩ :=
    exists_contDiff_top_localization (contDiffOn_top_of_harmonicOn hd hu hharm) hr hrR
  refine ⟨ρ', v, h1, h2, hv, hvu, fun y hy => ?_⟩
  rw [euclideanCoordLaplacian_congr_of_eqOn_open (isOpen_euclideanBall 0 ρ') hvu hy]
  exact hharm y (euclideanBall_mono (hr.trans h1).le h2.le hy)

/-- `D(r) = r⁻¹ ∫_{∂B_r} u (x · ∇u)`. -/
theorem energy_eq_inv_mul_sphereIntegral (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) =
      r⁻¹ * sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) := by
  have : NeZero d := ⟨hd.ne'⟩
  by_cases h1 : d = 1
  · subst h1
    exact energy_eq_inv_mul_sphereIntegral_one hu hharm hr hrR
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨ρ', v, h1, h2, hv, hvu, hvh⟩ := exists_harmonic_localization hd hr hrR hu hharm
    have hρ' : 0 < ρ' := hr.trans h1
    have hgrad : ∀ x ∈ euclideanBall (0 : Vec d) ρ',
        classicalGradient u x = classicalGradient v x := fun x hx =>
      (classicalGradient_congr_of_eqOn_open (isOpen_euclideanBall 0 ρ')
        (fun y hy => (hvu hy).symm) hx)
    have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) ρ' :=
      euclideanBall_mono hr.le h1.le
    have hD : ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) =
        ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient v x) :=
      setIntegral_congr_fun (isOpen_euclideanBall 0 r).measurableSet fun x hx => by
        rw [hgrad x (hsub hx)]
    have hS : sphereIntegral 0 r (fun x => u x * vecDot x (classicalGradient u x)) =
        sphereIntegral 0 r (fun x => v x * vecDot x (classicalGradient v x)) :=
      sphereIntegral_congr_of_eqOn hρ' (by rwa [abs_of_pos hr]) fun x hx => by
        simp only [hgrad x hx, hvu hx]
    rw [hD, hS]
    exact energy_eq_inv_mul_sphereIntegral_global hd2 hv hρ' hr h1 hvh

/-- The radial derivative of the sphere mean of `u²`: `m' = 2 D / (σ_d r^{d-1})`. -/
theorem hasDerivAt_sphereMean_sq (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    HasDerivAt (fun s => sphereMean 0 s (fun x => u x ^ 2))
      (2 * (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x)) /
        (sphereArea d * r ^ (d - 1))) r := by
  have : NeZero d := ⟨hd.ne'⟩
  by_cases h1 : d = 1
  · subst h1
    exact hasDerivAt_sphereMean_sq_one hu hharm hr hrR
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨ρ', v, h1, h2, hv, hvu, hvh⟩ := exists_harmonic_localization hd hr hrR hu hharm
    have hρ' : 0 < ρ' := hr.trans h1
    have hgrad : ∀ x ∈ euclideanBall (0 : Vec d) ρ',
        classicalGradient u x = classicalGradient v x := fun x hx =>
      (classicalGradient_congr_of_eqOn_open (isOpen_euclideanBall 0 ρ')
        (fun y hy => (hvu hy).symm) hx)
    have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) ρ' :=
      euclideanBall_mono hr.le h1.le
    have hD : ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) =
        ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient v x) :=
      setIntegral_congr_fun (isOpen_euclideanBall 0 r).measurableSet fun x hx => by
        rw [hgrad x (hsub hx)]
    rw [hD]
    refine (hasDerivAt_sphereMean_sq_global hd2 hv hρ' hr h1 hvh).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show -ρ' < r by linarith) h1] with s hs
    exact sphereMean_congr_of_eqOn hρ' (abs_lt.mpr hs) fun x hx => by simp only [hvu hx]

/-- `D'(r) = ∫_{∂B_r} |∇u|²`. -/
theorem hasDerivAt_energy (hd : 0 < d) {u : Vec d → ℝ} {R r : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    HasDerivAt (fun s => ∫ x in euclideanBall (0 : Vec d) s, vecNormSq (classicalGradient u x))
      (sphereIntegral 0 r (fun x => vecNormSq (classicalGradient u x))) r := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨ρ', v, h1, h2, hv, hvu, hvh⟩ := exists_harmonic_localization hd hr hrR hu hharm
  have hρ' : 0 < ρ' := hr.trans h1
  have hgrad : ∀ x ∈ euclideanBall (0 : Vec d) ρ',
      classicalGradient u x = classicalGradient v x := fun x hx =>
    (classicalGradient_congr_of_eqOn_open (isOpen_euclideanBall 0 ρ')
      (fun y hy => (hvu hy).symm) hx)
  have hg : Continuous fun x => vecNormSq (classicalGradient v x) :=
    continuous_vecNormSq.comp (ContDiff.continuous_classicalGradient
      (hv.of_le (by exact_mod_cast le_top)))
  have hS : sphereIntegral 0 r (fun x => vecNormSq (classicalGradient u x)) =
      sphereIntegral 0 r (fun x => vecNormSq (classicalGradient v x)) :=
    sphereIntegral_congr_of_eqOn hρ' (by rwa [abs_of_pos hr]) fun x hx => by
      simp only [hgrad x hx]
  rw [hS]
  refine (hasDerivAt_integral_euclideanBall hg hr).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hr h1] with s hs
  exact (setIntegral_congr_fun (isOpen_euclideanBall 0 s).measurableSet fun x hx => by
    rw [hgrad x (euclideanBall_mono hs.1.le hs.2.le hx)])

/-- `D` is continuous on `(0, R)`. -/
theorem continuousOn_energy (hd : 0 < d) {u : Vec d → ℝ} {R : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContinuousOn (fun s => ∫ x in euclideanBall (0 : Vec d) s, vecNormSq (classicalGradient u x))
      (Ioo 0 R) := fun _ hr =>
  (hasDerivAt_energy hd hu hharm hr.1 hr.2).continuousAt.continuousWithinAt

/-- `H(r) = ∫_{∂B_r} u²` is continuous on `(0, R)`. -/
theorem continuousOn_sphereIntegral_sq (hd : 0 < d) {u : Vec d → ℝ} {R : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContinuousOn (fun s => sphereIntegral 0 s (fun x => u x ^ 2)) (Ioo 0 R) := by
  have : NeZero d := ⟨hd.ne'⟩
  intro r hr
  obtain ⟨ρ', v, h1, h2, hv, hvu, hvh⟩ := exists_harmonic_localization hd hr.1 hr.2 hu hharm
  have hρ' : 0 < ρ' := hr.1.trans h1
  have hc := continuous_sphereIntegral (d := d) ((hv.continuous).pow 2) 0
  refine (hc.continuousAt.congr ?_).continuousWithinAt
  filter_upwards [Ioo_mem_nhds (show -ρ' < r by linarith [hr.1]) h1] with s hs
  exact sphereIntegral_congr_of_eqOn (f := fun x => v x ^ 2) (g := fun x => u x ^ 2) hρ'
    (abs_lt.mpr hs) fun x hx => by simp only [hvu hx]

/-- The sphere mean of `u²` is continuous on `(0, R)`. -/
theorem continuousOn_sphereMean_sq (hd : 0 < d) {u : Vec d → ℝ} {R : ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContinuousOn (fun s => sphereMean 0 s (fun x => u x ^ 2)) (Ioo 0 R) :=
  fun _ hr => (hasDerivAt_sphereMean_sq hd hu hharm hr.1 hr.2).continuousAt.continuousWithinAt

end

end PDE
