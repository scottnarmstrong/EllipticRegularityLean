module

public import PDEFoundation.PDE.HarmonicMeanValueLocal
public import PDEFoundation.PDE.HarmonicKernel
public import PDEFoundation.Analysis.HilbertPolar
public import PDEFoundation.Analysis.HilbertSubmean
public import PDEFoundation.Analysis.HilbertBallAverage
public import PDEFoundation.PDE.HarmonicEnergySmooth
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Integrating a radial weight against a function with constant spherical means -/

@[expose] public section

namespace PDE

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

private theorem sphereAverage_eq_center_of_ballMean [NeZero d]
    {u : HilbertVec d → ℝ} (hu : Continuous u) {R : ℝ}
    (hmean : ∀ r : ℝ, 0 < r → r < R →
      (volume (Metric.ball (0 : HilbertVec d) r)).toReal⁻¹ *
        ∫ z in Metric.ball (0 : HilbertVec d) r, u z = u 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    Internal.sphereAverage 0 r u = u 0 := by
  let A : ℝ → ℝ := fun t => t ^ (d - 1) * Internal.sphereAverage 0 t u
  let B : ℝ → ℝ := fun t => t ^ (d - 1) * u 0
  have hAc : Continuous A :=
    (continuous_pow _).mul (Internal.continuous_sphereAverage hu 0)
  have hBc : Continuous B := (continuous_pow _).mul continuous_const
  have hEq (t : ℝ) (ht : 0 < t) (htR : t < R) :
      (∫ q in (0 : ℝ)..t, A q) = ∫ q in (0 : ℝ)..t, B q := by
    have hnormal := Internal.normalizedIntegral_metricBall_eq_radialSphereAverage
      hu 0 ht
    rw [hmean t ht htR] at hnormal
    have hconst := Internal.normalizedIntegral_metricBall_eq_radialSphereAverage
      (u := fun _ : HilbertVec d => u 0) continuous_const 0 ht
    have hvol : (volume (Metric.ball (0 : HilbertVec d) t)).toReal ≠ 0 := by
      rw [Internal.volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div 0 ht]
      exact mul_ne_zero Internal.sphereMeasure_real_univ_ne_zero
        (div_ne_zero (pow_ne_zero _ ht.ne') (by exact_mod_cast NeZero.ne d))
    have hconstval : (volume (Metric.ball (0 : HilbertVec d) t)).toReal⁻¹ *
        ∫ z in Metric.ball (0 : HilbertVec d) t, (u 0 : ℝ) = u 0 := by
      rw [setIntegral_const]
      change (volume (Metric.ball (0 : HilbertVec d) t)).toReal⁻¹ *
        ((volume (Metric.ball (0 : HilbertVec d) t)).toReal * u 0) = u 0
      field_simp
    rw [hconstval] at hconst
    simp only [Internal.sphereAverage_const] at hconst
    change u 0 = (d : ℝ) / t ^ d * ∫ q in (0 : ℝ)..t, B q at hconst
    change u 0 = (d : ℝ) / t ^ d * ∫ q in (0 : ℝ)..t, A q at hnormal
    have hfactor : (d : ℝ) / t ^ d ≠ 0 :=
      div_ne_zero (by exact_mod_cast NeZero.ne d) (pow_ne_zero _ ht.ne')
    exact mul_left_cancel₀ hfactor (hnormal.symm.trans hconst)
  have hev : (fun t => ∫ q in (0 : ℝ)..t, A q) =ᶠ[nhds r]
      (fun t => ∫ q in (0 : ℝ)..t, B q) := by
    filter_upwards [Ioo_mem_nhds hr hrR] with t ht
    exact hEq t ht.1 ht.2
  have hDA := intervalIntegral.integral_hasDerivAt_right
    (hAc.intervalIntegrable 0 r) (hAc.stronglyMeasurableAtFilter volume (nhds r))
      hAc.continuousAt
  have hDB := intervalIntegral.integral_hasDerivAt_right
    (hBc.intervalIntegrable 0 r) (hBc.stronglyMeasurableAtFilter volume (nhds r))
      hBc.continuousAt
  have hval : A r = B r := hDA.unique (hDB.congr_of_eventuallyEq hev)
  exact mul_left_cancel₀ (pow_ne_zero _ hr.ne') hval

private theorem radial_integral_eq_center_mul [NeZero d]
    {F : ℝ → ℝ} (hF : Continuous F)
    (hFsupp : HasCompactSupport
      (fun z : HilbertVec d => F (‖z‖ ^ 2)))
    {u : HilbertVec d → ℝ} (hu : Continuous u)
    (havg : ∀ r : ℝ, 0 < r → F (r ^ 2) ≠ 0 →
      Internal.sphereAverage 0 r u = u 0) :
    (∫ z : HilbertVec d, F (‖z‖ ^ 2) * u z) =
      u 0 * ∫ z : HilbertVec d, F (‖z‖ ^ 2) := by
  let K : HilbertVec d → ℝ := fun z => F (‖z‖ ^ 2)
  have hK : Continuous K := hF.comp (continuous_norm.pow 2)
  have hGint : Integrable (fun z : HilbertVec d => K z * u z) :=
    (hK.mul hu).integrable_of_hasCompactSupport hFsupp.mul_right
  have hKint : Integrable K := hK.integrable_of_hasCompactSupport hFsupp
  have hpoint (r : ℝ) (hr : 0 < r) :
      (∫ ω : Metric.sphere (0 : HilbertVec d) 1,
        K (r • (ω : HilbertVec d)) * u (r • (ω : HilbertVec d))
          ∂Internal.sphereMeasure d) =
      u 0 * (∫ ω : Metric.sphere (0 : HilbertVec d) 1,
        K (r • (ω : HilbertVec d)) ∂Internal.sphereMeasure d) := by
    have hω (ω : Metric.sphere (0 : HilbertVec d) 1) :
        K (r • (ω : HilbertVec d)) = F (r ^ 2) := by
      simp [K, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        mem_sphere_zero_iff_norm.mp ω.2]
    simp_rw [hω]
    by_cases hzero : F (r ^ 2) = 0
    · simp [hzero]
    · rw [integral_const_mul]
      have hsphere := Internal.integral_sphere_eq_measureReal_smul_sphereAverage
        u (0 : HilbertVec d) r
      simp only [zero_add, smul_eq_mul] at hsphere
      rw [hsphere, havg r hr hzero]
      simp only [integral_const, smul_eq_mul]
      ring
  have hpolarG := Internal.integral_eq_integral_Ioi_sphere hGint
  have hpolarK := Internal.integral_eq_integral_Ioi_sphere hKint
  change (∫ z, K z * u z) = u 0 * ∫ z, K z
  rw [hpolarG, hpolarK, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
    change r ^ (d - 1) • (∫ ω, K (r • (ω : HilbertVec d)) *
        u (r • (ω : HilbertVec d)) ∂Internal.sphereMeasure d) =
      u 0 * (r ^ (d - 1) •
        ∫ ω, K (r • (ω : HilbertVec d)) ∂Internal.sphereMeasure d)
    rw [hpoint r hr]
    simp [smul_eq_mul, mul_left_comm])

private theorem contDiff_cutoff_mul_local
    {x : Vec d} {r R : ℝ} {v : Vec d → ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y => canonicalBallCutoff x r R y * v y) := by
  let φ := canonicalBallCutoff x r R
  let f : Vec d → ℝ := fun y => φ y * v y
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    canonicalBallCutoff_smooth x hr hrR
  have hB : IsOpen (euclideanBall x R) := isOpen_euclideanBall x R
  have hT : IsOpen ((tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl
  have hinside : ContDiffOn ℝ (⊤ : ℕ∞) f (euclideanBall x R) :=
    hφ.contDiffOn.mul hv
  have houtside : ContDiffOn ℝ (⊤ : ℕ∞) f ((tsupport φ)ᶜ) := by
    have hzero : EqOn f (fun _ : Vec d => (0 : ℝ)) ((tsupport φ)ᶜ) := by
      intro y hy
      have hyφ : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [f, hyφ]
    exact (contDiffOn_congr hzero).2 contDiffOn_const
  have hcover : euclideanBall x R ∪ (tsupport φ)ᶜ = Set.univ := by
    ext y
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hy : y ∈ tsupport φ
    · left
      exact canonicalBallCutoff_tsupport_subset_outer hr hrR hy
    · exact Or.inr hy
  dsimp [f, φ] at hinside houtside ⊢
  exact contDiff_of_contDiffOn_union_of_isOpen hinside houtside hcover hB hT

private theorem integralAverage_reflected_ball
    (x : Vec d) (v : Vec d → ℝ) (r : ℝ) :
    integralAverage (euclideanBall (0 : Vec d) r) (fun y => v (x - y)) =
      integralAverage (euclideanBall x r) v := by
  let T : Vec d → Vec d := fun y => x - y
  have hpre : T ⁻¹' euclideanBall x r = euclideanBall (0 : Vec d) r := by
    ext y
    change euclideanSqDist (T y) x < r ^ 2 ↔
      euclideanSqDist y (0 : Vec d) < r ^ 2
    have hsub : T y - x = -(y - (0 : Vec d)) := by
      dsimp [T]
      abel
    rw [euclideanSqDist, hsub, vecNormSq_neg, euclideanSqDist]
  have hpres : MeasurePreserving T (volume : Measure (Vec d)) volume :=
    Measure.measurePreserving_sub_left volume x
  have hvol : volume (euclideanBall (0 : Vec d) r) =
      volume (euclideanBall x r) := by
    rw [← hpre]
    exact hpres.measure_preimage
      (isOpen_euclideanBall x r).measurableSet.nullMeasurableSet
  have hint : (∫ y in euclideanBall (0 : Vec d) r, v (x - y)) =
      ∫ y in euclideanBall x r, v y := by
    rw [← hpre]
    exact hpres.setIntegral_preimage_emb
      (Homeomorph.subLeft x).measurableEmbedding v (euclideanBall x r)
  unfold integralAverage
  rw [hvol, hint]

/-- A smooth harmonic function is reproduced at the center by the scaled
Euclidean-radial kernel. -/
theorem integral_harmonicKernelScaled_mul_eq_of_harmonicOn (hd : 0 < d)
    {v : Vec d → ℝ} {x : Vec d} {R s : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ y ∈ euclideanBall x R, euclideanCoordLaplacian v y = 0)
    (hs : 0 < s) (hsR : s < R) :
    (∫ y, harmonicKernelScaled s y * v (x - y)) = v x := by
  let _ : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let t : ℝ := (s + R) / 2
  have hst : s < t := by dsimp [t]; linarith
  have htR : t < R := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := le_of_lt (hs.trans hst)
  let w : Vec d → ℝ := fun z => canonicalBallCutoff x t R z * v z
  have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
    contDiff_cutoff_mul_local ht0 htR hv
  have hweq : EqOn w v (euclideanBall x t) := by
    intro z hz
    change canonicalBallCutoff x t R z * v z = v z
    rw [canonicalBallCutoff_eq_one_on_inner ht0 htR hz, one_mul]
  have hx : x ∈ euclideanBall x t := center_mem_euclideanBall x (hs.trans hst)
  have hwx : w x = v x := hweq hx
  let P : ℝ → ℝ := harmonicKernelScaledProfile d s
  have hPc : Continuous P := (harmonicKernelScaledProfile_smooth d s).continuous
  have hPsupp : HasCompactSupport
      (fun z : HilbertVec d => P (‖z‖ ^ 2)) := by
    apply HasCompactSupport.intro (K := Metric.closedBall (0 : HilbertVec d) s)
      (isCompact_closedBall (0 : HilbertVec d) s)
    intro z hz
    have hzle : s < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact harmonicKernelScaledProfile_zero_of_scale_squared_le hs (by nlinarith)
  let u : HilbertVec d → ℝ :=
    fun z => w (x - Internal.toHilbert.symm z)
  have hu : Continuous u :=
    hw.continuous.comp (continuous_const.sub Internal.toHilbert.symm.continuous)
  have hmean : ∀ r : ℝ, 0 < r → r < t →
      (volume (Metric.ball (0 : HilbertVec d) r)).toReal⁻¹ *
        ∫ z in Metric.ball (0 : HilbertVec d) r, u z = u 0 := by
    intro r hr hrt
    have hreflect := integralAverage_reflected_ball x w r
    have hcut : integralAverage (euclideanBall x r) w =
        integralAverage (euclideanBall x r) v := by
      apply integralAverage_congr_ae
      filter_upwards [ae_restrict_mem (isOpen_euclideanBall x r).measurableSet]
        with z hz
      exact hweq ((euclideanBall_mono hr.le hrt.le) hz)
    have hlocal := integralAverage_euclideanBall_eq_center_of_harmonicOn
      hd hv hharm hr (hrt.trans htR)
    have hdict := integralAverage_euclideanBall_eq_hilbert
      (fun y => w (x - y)) (0 : Vec d) hr
    simp only [map_zero] at hdict
    change integralAverage (euclideanBall (0 : Vec d) r)
      (fun y => w (x - y)) =
      (volume (Metric.ball (0 : HilbertVec d) r)).toReal⁻¹ *
        ∫ z in Metric.ball (0 : HilbertVec d) r, u z at hdict
    rw [← hdict, hreflect, hcut, hlocal]
    have hzero : Internal.toHilbert.symm (0 : HilbertVec d) = (0 : Vec d) :=
      map_zero _
    change v x = w (x - Internal.toHilbert.symm (0 : HilbertVec d))
    rw [hzero, sub_zero]
    exact hwx.symm
  have havg : ∀ r : ℝ, 0 < r → P (r ^ 2) ≠ 0 →
      Internal.sphereAverage 0 r u = u 0 := by
    intro r hr hP
    have hrs : r < s := by
      by_contra hn
      have hsqr : s ^ 2 ≤ r ^ 2 := by nlinarith
      exact hP (harmonicKernelScaledProfile_zero_of_scale_squared_le hs hsqr)
    exact sphereAverage_eq_center_of_ballMean hu hmean hr (hrs.trans hst)
  have hradial := radial_integral_eq_center_mul hPc hPsupp hu havg
  have hnorm (y : Vec d) :
      ‖Internal.toHilbert y‖ ^ 2 = vecNormSq y := by
    rw [Internal.toHilbert_apply, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec,
      vecEuclideanNorm_sq]
  have hkernel (y : Vec d) :
      harmonicKernelScaled s y = P (‖Internal.toHilbert y‖ ^ 2) := by
    rw [harmonicKernelScaled_eq_profile, hnorm]
  have htransport :
      (∫ y : Vec d, harmonicKernelScaled s y * w (x - y)) =
        ∫ z : HilbertVec d, P (‖z‖ ^ 2) * u z := by
    have h := Internal.measurePreserving_toHilbert.integral_comp
      Internal.toHilbert.toHomeomorph.measurableEmbedding
      (fun z : HilbertVec d => P (‖z‖ ^ 2) * u z)
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply,
      ← hkernel, u] using h
  have htransportK :
      (∫ y : Vec d, harmonicKernelScaled s y) =
        ∫ z : HilbertVec d, P (‖z‖ ^ 2) := by
    have h := Internal.measurePreserving_toHilbert.integral_comp
      Internal.toHilbert.toHomeomorph.measurableEmbedding
      (fun z : HilbertVec d => P (‖z‖ ^ 2))
    simpa only [Function.comp_apply, hkernel] using h
  have hpatch : (∫ y, harmonicKernelScaled s y * v (x - y)) =
      ∫ y, harmonicKernelScaled s y * w (x - y) := by
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ euclideanBall (0 : Vec d) s
    · have hxy : x - y ∈ euclideanBall x s := by
        have hsub : (x - y) - x = -(y - (0 : Vec d)) := by abel
        change euclideanSqDist (x - y) x < s ^ 2
        change euclideanSqDist y (0 : Vec d) < s ^ 2 at hy
        simpa only [euclideanSqDist, hsub, vecNormSq_neg] using hy
      rw [hweq ((euclideanBall_mono hs.le hst.le) hxy)]
    · have hzero : harmonicKernelScaled s y = 0 := by
        rw [harmonicKernelScaled_eq_profile]
        apply harmonicKernelScaledProfile_zero_of_scale_squared_le hs
        change ¬euclideanSqDist y (0 : Vec d) < s ^ 2 at hy
        simpa only [euclideanSqDist, sub_zero] using le_of_not_gt hy
      simp [hzero]
  rw [hpatch, htransport, hradial, ← htransportK,
    harmonicKernelScaled_integral_eq_one hs, mul_one]
  have hzero : Internal.toHilbert.symm (0 : HilbertVec d) = (0 : Vec d) :=
    map_zero _
  change w (x - Internal.toHilbert.symm (0 : HilbertVec d)) = v x
  rw [hzero, sub_zero]
  exact hwx

/-- The radial kernel reproduces a harmonic function throughout the interior
ball that remains after a margin of `s` is removed. -/
theorem integral_harmonicKernelScaled_mul_eq_on_innerBall (hd : 0 < d)
    {v : Vec d → ℝ} {x : Vec d} {R s : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ y ∈ euclideanBall x R, euclideanCoordLaplacian v y = 0)
    (hs : 0 < s) (hsR : s < R)
    {x' : Vec d} (hx' : x' ∈ euclideanBall x (R - s)) :
    (∫ y, harmonicKernelScaled s y * v (x' - y)) = v x' := by
  have hmargin : 0 < R - s := by linarith
  have hdist := (mem_euclideanBall_iff_vecEuclideanNorm_lt hmargin).mp hx'
  let r : ℝ := R - vecEuclideanNorm (x' - x)
  have hsr : s < r := by dsimp [r]; linarith
  have hr : 0 < r := hs.trans hsr
  have hR : 0 < R := hs.trans hsR
  have hsubset : euclideanBall x' r ⊆ euclideanBall x R :=
    euclideanBall_subset_of_center_norm_add_le hr hR (by dsimp [r]; ring_nf; exact le_rfl)
  exact integral_harmonicKernelScaled_mul_eq_of_harmonicOn hd
    (hv.mono hsubset) (fun y hy => hharm y (hsubset hy)) hs hsr

end

end PDE
