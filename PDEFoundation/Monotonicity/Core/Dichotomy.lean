module

public import PDEFoundation.Monotonicity.Core.FrequencyDerivs
public import PDEFoundation.Monotonicity.Core.HarmonicFacade
public import PDEFoundation.Monotonicity.Core.Bridge

/-!
# Chapter 2: the dichotomy for harmonic functions on a ball

For `u` of class `C²` and harmonic on `B_R ⊆ ℝᵈ` (`d ≥ 1`) with `H(r) = ∫_{∂B_r} u²`:

* `0 ≤ H(r)`;
* `H(r) = 0` for some `0 < r < R` forces `u = 0` on `B_r` (`D(r) = r⁻¹ ∫_{∂B_r} u (x·∇u) = 0`
  because `u = 0` almost everywhere on the sphere, so `∇u = 0`, `u` is constant, and the constant
  vanishes by continuity of `H`);
* either `u = 0` on `B_R` or `H(r) > 0` for all `r ∈ (0, R)`;
* if `u = 0` on `B_R` then `almgrenFrequency u r = 0`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

theorem sphereIntegral_nonneg {r : ℝ} (hr : 0 ≤ r) {f : Vec d → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ sphereIntegral 0 r f := by
  unfold sphereIntegral
  exact mul_nonneg (pow_nonneg hr _) (integral_nonneg fun ω => hf _)

theorem sphereIntegral_const [NeZero d] (s c : ℝ) :
    sphereIntegral (0 : Vec d) s (fun _ => c) = sphereArea d * s ^ (d - 1) * c := by
  rw [sphereIntegral_eq_mul_sphereMean]
  congr 1
  unfold sphereMean
  have : IsFiniteMeasure ((volume : Measure (HilbertVec d)).toSphere) := inferInstance
  have : NeZero ((volume : Measure (HilbertVec d)).toSphere) := by
    refine ⟨fun h => ?_⟩
    have := sphereArea_pos (d := d)
    simp [sphereArea, Internal.sphereMeasure, Measure.real, h] at this
  exact average_const _ c

/-- If `u² ` has vanishing sphere integral then every product `u * f` does. -/
theorem sphereIntegral_mul_eq_zero_of_sq {u : Vec d → ℝ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContinuousOn u (euclideanBall 0 R))
    (hH : sphereIntegral 0 r (fun x => u x ^ 2) = 0) (f : Vec d → ℝ) :
    sphereIntegral 0 r (fun x => u x * f x) = 0 := by
  unfold sphereIntegral at hH ⊢
  have hpow : r ^ (d - 1) ≠ 0 := (pow_pos hr _).ne'
  have h0 := (mul_eq_zero.mp hH).resolve_left hpow
  have hmem : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
      (0 : Vec d) + r • (ω : HilbertVec d).toVec ∈ euclideanBall 0 R := fun ω => by
    have := smul_toVec_mem_euclideanBall (d := d) (ρ := R) (s := r) (hr.trans hrR)
      (by rwa [abs_of_pos hr]) ω
    exact this
  have hcont : Continuous fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      u ((0 : Vec d) + r • (ω : HilbertVec d).toVec) := by
    have h1 : Continuous fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
        (0 : Vec d) + r • (ω : HilbertVec d).toVec :=
      continuous_const.add (Continuous.const_smul (continuous_toVec.comp continuous_subtype_val) r)
    exact hu.comp_continuous h1 hmem
  have hint : Integrable (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      u ((0 : Vec d) + r • (ω : HilbertVec d).toVec) ^ 2)
      ((volume : Measure (HilbertVec d)).toSphere) :=
    (hcont.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).mp h0
  rw [mul_eq_zero]
  right
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with ω hω
  have h1 : u ((0 : Vec d) + r • (ω : HilbertVec d).toVec) = 0 := by
    simpa using hω
  show u ((0 : Vec d) + r • (ω : HilbertVec d).toVec) * _ = 0
  rw [h1, zero_mul]

section Harmonic

variable {u : Vec d → ℝ} {R : ℝ}

theorem continuousOn_vecNormSq_classicalGradient (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContinuousOn (fun x => vecNormSq (classicalGradient u x)) (euclideanBall 0 R) := by
  simp_rw [vecNormSq_eq_sum_sq]
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact ((contDiffOn_classicalGradient_apply_of_harmonicOn hd hu hharm i).continuousOn).pow 2

/-- Vanishing energy on an inner ball forces `u` to be constant there. -/
theorem eq_const_of_energy_eq_zero (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hD : ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) = 0) :
    ∀ x ∈ euclideanBall (0 : Vec d) r, u x = u 0 := by
  have hcont := continuousOn_vecNormSq_classicalGradient hd hu hharm
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall 0 R := euclideanBall_mono hr.le hrR.le
  have hint : IntegrableOn (fun x => vecNormSq (classicalGradient u x))
      (euclideanBall (0 : Vec d) r) := by
    have hc : euclideanClosedBall (0 : Vec d) r ⊆ euclideanBall 0 R :=
      euclideanClosedBall_subset_euclideanBall hr.le hrR
    exact ((hcont.mono hc).integrableOn_compact (isCompact_euclideanClosedBall 0 hr.le)).mono_set
      (euclideanBall_subset_euclideanClosedBall 0 r)
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall
    fun x => vecNormSq_nonneg _) hint).mp hD
  have hzero : EqOn (fun x => vecNormSq (classicalGradient u x)) (fun _ => (0 : ℝ))
      (euclideanBall (0 : Vec d) r) :=
    Measure.eqOn_open_of_ae_eq hae (isOpen_euclideanBall 0 r) (hcont.mono hsub)
      continuousOn_const
  have hdiff : DifferentiableOn ℝ u (euclideanBall (0 : Vec d) r) :=
    (hu.differentiableOn (by norm_num)).mono hsub
  have hfd : ∀ x ∈ euclideanBall (0 : Vec d) r,
      fderivWithin ℝ u (euclideanBall (0 : Vec d) r) x = 0 := by
    intro x hx
    rw [fderivWithin_of_isOpen (isOpen_euclideanBall 0 r) hx]
    have hg : classicalGradient u x = 0 := vecNormSq_eq_zero (hzero hx)
    ext v
    rw [fderiv_apply_eq_vecDot_classicalGradient, hg]
    simp [vecDot]
  intro x hx
  exact (convex_euclideanBall 0 r).is_const_of_fderivWithin_eq_zero hdiff hfd hx
    (center_mem_euclideanBall 0 hr)

/-- Zero boundary values in the `L²` sense force `u = 0` on the ball. -/
theorem eqOn_zero_of_sphereIntegral_sq_eq_zero (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hH : sphereIntegral 0 r (fun x => u x ^ 2) = 0) :
    ∀ x ∈ euclideanBall (0 : Vec d) r, u x = 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hD : ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) = 0 := by
    rw [energy_eq_inv_mul_sphereIntegral hd hu hharm hr hrR,
      sphereIntegral_mul_eq_zero_of_sq hr hrR hu.continuousOn hH, mul_zero]
  have hconst := eq_const_of_energy_eq_zero hd hu hharm hr hrR hD
  set c := u 0 with hc
  have hFc : EqOn (fun s => sphereIntegral 0 s (fun x => u x ^ 2))
      (fun s => sphereArea d * s ^ (d - 1) * c ^ 2) (Ioo 0 r) := by
    intro s hs
    have hs' : |s| < r := by rw [abs_of_pos hs.1]; exact hs.2
    have := sphereIntegral_congr_of_eqOn (f := fun x => u x ^ 2) (g := fun _ => c ^ 2) hr hs'
      fun x hx => by simp only [hconst x hx]
    exact this.trans (sphereIntegral_const s (c ^ 2))
  have hsubR : Ioc 0 r ⊆ Ioo 0 R := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hrR⟩
  have hFcont := (continuousOn_sphereIntegral_sq hd hu hharm).mono hsubR
  have hGcont : ContinuousOn (fun s : ℝ => sphereArea d * s ^ (d - 1) * c ^ 2) (Ioc 0 r) :=
    (((continuous_const.mul (continuous_pow _)).mul continuous_const)).continuousOn
  have hext := Set.EqOn.of_subset_closure hFc hFcont hGcont Ioo_subset_Ioc_self
    (by rw [closure_Ioo hr.ne]; exact fun s hs => ⟨hs.1.le, hs.2⟩)
  have hr' := hext (show r ∈ Ioc 0 r from ⟨hr, le_rfl⟩)
  simp only at hr'
  rw [hH] at hr'
  have hpos : 0 < sphereArea d * r ^ (d - 1) := mul_pos sphereArea_pos (pow_pos hr _)
  have hc2 : c ^ 2 = 0 := by
    rcases mul_eq_zero.mp hr'.symm with h | h
    · exact absurd h hpos.ne'
    · exact h
  intro x hx
  rw [hconst x hx]
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hc2

/-- The dichotomy: either `u ≡ 0` on `B_R`, or `H(r) > 0` for every `r ∈ (0, R)`. -/
theorem dichotomy_zero_or_sphereIntegral_sq_pos (hd : 0 < d)
    (hu : ContDiffOn ℝ 2 u (euclideanBall 0 R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    (∀ x ∈ euclideanBall (0 : Vec d) R, u x = 0) ∨
      ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2) := by
  by_cases h : ∀ r ∈ Ioo (0 : ℝ) R, 0 < sphereIntegral 0 r (fun x => u x ^ 2)
  · exact Or.inr h
  left
  push Not at h
  obtain ⟨r, hr, hle⟩ := h
  have h0 : sphereIntegral 0 r (fun x => u x ^ 2) = 0 :=
    le_antisymm hle (sphereIntegral_nonneg hr.1.le fun x => sq_nonneg _)
  have hin := eqOn_zero_of_sphereIntegral_sq_eq_zero hd hu hharm hr.1 hr.2 h0
  have hz : ContDiffOn ℝ 2 (fun _ : Vec d => (0 : ℝ)) (euclideanBall (0 : Vec d) R) :=
    contDiffOn_const
  have hzh : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian (fun _ : Vec d => (0 : ℝ)) x = 0 := by
    intro x _
    have h1 : ∀ i, euclideanCoordDeriv i (fun _ : Vec d => (0 : ℝ)) = fun _ => 0 := by
      intro i
      ext y
      simp [euclideanCoordDeriv]
    simp [euclideanCoordLaplacian, euclideanCoordSecondDeriv, h1]
  exact eqOn_euclideanBall_of_harmonic_eqOn_inner hd hr.1 hr.2.le hu hharm hz hzh hin

/-- If `u ≡ 0` on `B_R` the Almgren frequency vanishes on `(0, R)`. -/
theorem almgrenFrequency_eq_zero_of_eqOn_zero
    (h : ∀ x ∈ euclideanBall (0 : Vec d) R, u x = 0) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) R) :
    almgrenFrequency u r = 0 := by
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall 0 R := euclideanBall_mono hr.1.le hr.2.le
  have hg : ∀ x ∈ euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) = 0 := by
    intro x hx
    have := classicalGradient_congr_of_eqOn_open (isOpen_euclideanBall 0 R)
      (g := fun _ => (0 : ℝ)) (fun y hy => h y hy) (hsub hx)
    rw [this]
    simp [classicalGradient, vecNormSq, vecDot]
  have hI : ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) = 0 := by
    rw [setIntegral_congr_fun (isOpen_euclideanBall 0 r).measurableSet hg]
    simp
  unfold almgrenFrequency
  rw [hI]
  simp

end Harmonic

end

end PDE
