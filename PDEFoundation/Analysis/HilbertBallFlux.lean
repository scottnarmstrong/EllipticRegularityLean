module

public import PDEFoundation.Analysis.HilbertRadialTest
public import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement

/-! # Radial flux and ball Laplacian identities -/

@[expose] public section

namespace PDE.Internal

open MeasureTheory Metric Set InnerProductSpace
open scoped Laplacian

noncomputable section

variable {d : ℕ}

local notation "𝔼" => HilbertVec d

/-- Polar coordinates for a Laplacian paired with a compactly supported
radial test.  This is the right-hand-side conversion needed to identify the
weak radial derivative of the weighted spherical flux. -/
theorem integral_laplacian_mul_radial_eq_sphereAverage [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) (x : 𝔼)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcompact : HasCompactSupport (fun y : 𝔼 => φ (‖y - x‖ ^ 2))) :
    ∫ y, Δ u y * φ (‖y - x‖ ^ 2) =
      (sphereMeasure d).real Set.univ *
        ∫ s in Ioi (0 : ℝ), s ^ (d - 1) * sphereAverage x s (Δ u) * φ (s ^ 2) := by
  let G : 𝔼 → ℝ := fun z => Δ u (x + z) * φ (‖z‖ ^ 2)
  have hΔ : Continuous (Δ u) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    have hiter : Continuous (iteratedFDeriv ℝ 2 u) :=
      hu.continuous_iteratedFDeriv (by norm_num)
    fun_prop
  have hradial : Continuous (fun y : 𝔼 => φ (‖y‖ ^ 2)) := by
    exact hφ.continuous.comp (continuous_norm.pow 2)
  have hGcont : Continuous G := (hΔ.comp (continuous_const.add continuous_id)).mul hradial
  have hradialCompact : HasCompactSupport (fun z : 𝔼 => φ (‖z‖ ^ 2)) := by
    have htranslate : (fun z : 𝔼 => φ (‖z‖ ^ 2)) =
        (fun y : 𝔼 => φ (‖y - x‖ ^ 2)) ∘ (Homeomorph.addLeft x) := by
      funext z
      simp
    rw [htranslate]
    exact hcompact.comp_homeomorph (Homeomorph.addLeft x)
  have hGcompact : HasCompactSupport G := hradialCompact.mul_left
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGcompact
  have htrans : ∫ z, G z = ∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
    have h := integral_add_left_eq_self (μ := (volume : Measure 𝔼))
      (fun y : 𝔼 => Δ u y * φ (‖y - x‖ ^ 2)) x
    simpa only [G, add_sub_cancel_left] using h
  have hpolar := integral_eq_integral_Ioi_sphere (G := G) hGint
  have hinner : ∀ s ∈ Ioi (0 : ℝ),
      ∫ ω, G (s • (ω : 𝔼)) ∂(sphereMeasure d) =
        (sphereMeasure d).real Set.univ * sphereAverage x s (Δ u) * φ (s ^ 2) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hfun : (fun ω : sphere (0 : 𝔼) 1 => G (s • (ω : 𝔼))) =
        fun ω : sphere (0 : 𝔼) 1 =>
          Δ u (x + s • (ω : 𝔼)) * φ (s ^ 2) := by
      funext ω
      simp only [G]
      have hnorm : ‖s • (ω : 𝔼)‖ = s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0,
          mem_sphere_zero_iff_norm.mp ω.2, mul_one]
      rw [hnorm]
    rw [hfun, integral_mul_const,
      integral_sphere_eq_measureReal_smul_sphereAverage, smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => by rw [hinner s hs])] at hpolar
  rw [← htrans, hpolar]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [smul_eq_mul]
  ring

/-- Exact distributional pairing of the weighted spherical flux with an
arbitrary smooth radius test supported in a positive annulus. -/
theorem integral_deriv_mul_weightedSphereFlux_eq_neg_laplacianProfile [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) (x : 𝔼) {R : ℝ}
    {p : ℝ → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R)
    (hpsupp : tsupport p ⊆ Ioo a b) :
    ∫ s in Ioi (0 : ℝ), deriv p s * (s ^ (d - 1) * sphereFlux x s u) =
      -(sphereMeasure d).real Set.univ *
        ∫ s in Ioi (0 : ℝ),
          p s * (s ^ (d - 1) * sphereAverage x s (Δ u)) := by
  let φ : ℝ → ℝ := sqrtPullback p
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    contDiff_sqrtPullback_of_tsupport_subset_Ioo hp ha hpsupp
  let r : ℝ := (b + R) / 2
  have hr0 : 0 < r := by dsimp only [r]; linarith only [ha, hab, hbR]
  have hbr : b < r := by dsimp only [r]; linarith only [hbR]
  have hrR : r < R := by dsimp only [r]; linarith only [hbR]
  have hradial := radial_sqrtPullback_hasCompactSupport_and_tsupport_subset_ball
    ha (ha.trans hab) hbr hpsupp x
  have hflux := integral_Ioi_test_sphereFlux_eq_neg_integral_laplacian
    hu hφ hradial.1 hr0 hrR hradial.2
  have hlap := integral_laplacian_mul_radial_eq_sphereAverage
    hu x hφ hradial.1
  rw [hlap] at hflux
  have hleft :
      (∫ s in Ioi (0 : ℝ),
        2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u)) =
      ∫ s in Ioi (0 : ℝ),
        deriv p s * (s ^ (d - 1) * sphereFlux x s u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change 2 * s * deriv φ (s ^ 2) * _ = deriv p s * _
    rw [show 2 * s * deriv φ (s ^ 2) = deriv p s from
      two_mul_mul_deriv_sqrtPullback_sq (hp.of_le (by norm_num)) hs]
  have hright :
      (∫ s in Ioi (0 : ℝ),
        s ^ (d - 1) * sphereAverage x s (Δ u) * φ (s ^ 2)) =
      ∫ s in Ioi (0 : ℝ),
        p s * (s ^ (d - 1) * sphereAverage x s (Δ u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change s ^ (d - 1) * sphereAverage x s (Δ u) * φ (s ^ 2) =
      p s * (s ^ (d - 1) * sphereAverage x s (Δ u))
    rw [show φ (s ^ 2) = p s from sqrtPullback_sq hs.le]
    ring
  rw [hleft, hright] at hflux
  rw [hflux]
  ring

/-- On every annulus away from the origin, the dimension-weighted spherical
flux has weak derivative equal to the correspondingly weighted spherical
average of the Laplacian. -/
theorem weightedSphereFlux_hasWeakDerivOnIoo [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) (x : 𝔼) {R a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbR : b < R) :
    PDE.HasWeakDerivOnIoo a b
      (fun s => s ^ (d - 1) * sphereFlux x s u)
      (fun s => (sphereMeasure d).real Set.univ *
        (s ^ (d - 1) * sphereAverage x s (Δ u))) := by
  unfold PDE.HasWeakDerivOnIoo PDE.HasWeakPartialDerivOn
  intro ψ hψ hψcompact hψsupport
  let p : ℝ → ℝ := PDE.scalarPullbackOne ψ
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := PDE.ContDiff.scalarPullbackOne hψ
  have hpsupp : tsupport p ⊆ Ioo a b :=
    PDE.tsupport_scalarPullbackOne_subset_Ioo hψsupport
  have hpair := integral_deriv_mul_weightedSphereFlux_eq_neg_laplacianProfile
    hu x hp ha hab hbR hpsupp
  have hpzero : ∀ s ∉ Ioo a b, p s = 0 := by
    intro s hs
    exact image_eq_zero_of_notMem_tsupport (fun h => hs (hpsupp h))
  have hdpzero : ∀ s ∉ Ioo a b, deriv p s = 0 := by
    intro s hs
    by_contra hne
    exact hs (hpsupp (support_deriv_subset hne))
  have hleft :
      (∫ s in Ioi (0 : ℝ), deriv p s *
        (s ^ (d - 1) * sphereFlux x s u)) =
      ∫ s in Ioo a b, deriv p s *
        (s ^ (d - 1) * sphereFlux x s u) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with s
    by_cases hs : s ∈ Ioo a b
    · rw [indicator_of_mem hs, indicator_of_mem (show s ∈ Ioi 0 from ha.trans hs.1)]
    · rw [indicator_of_notMem hs]
      by_cases hs0 : s ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hs0, hdpzero s hs, zero_mul]
      · rw [indicator_of_notMem hs0]
  have hright :
      (∫ s in Ioi (0 : ℝ), p s *
        (s ^ (d - 1) * sphereAverage x s (Δ u))) =
      ∫ s in Ioo a b, p s *
        (s ^ (d - 1) * sphereAverage x s (Δ u)) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with s
    by_cases hs : s ∈ Ioo a b
    · rw [indicator_of_mem hs, indicator_of_mem (show s ∈ Ioi 0 from ha.trans hs.1)]
    · rw [indicator_of_notMem hs]
      by_cases hs0 : s ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hs0, hpzero s hs, zero_mul]
      · rw [indicator_of_notMem hs0]
  rw [hleft, hright] at hpair
  have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  rw [PDE.setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne,
    PDE.setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne]
  simp only [PDE.scalarPullbackOne, PDE.liftOneDimensional,
    PDE.vecOneCoordinate_scalarToVecOne]
  have hpderiv : ∀ t, deriv p t =
      (fderiv ℝ ψ (PDE.scalarToVecOne t)) (PDE.basisVec (0 : Fin 1)) := by
    intro t
    exact PDE.deriv_scalarPullbackOne_eq_native_directional hψone t
  simp_rw [hpderiv] at hpair
  rw [← integral_const_mul] at hpair
  rw [← integral_neg]
  calc
    (∫ t in Ioo a b,
        t ^ (d - 1) * sphereFlux x t u *
          (fderiv ℝ ψ (PDE.scalarToVecOne t)) (PDE.basisVec (0 : Fin 1))) =
        ∫ t in Ioo a b,
          (fderiv ℝ ψ (PDE.scalarToVecOne t)) (PDE.basisVec (0 : Fin 1)) *
            (t ^ (d - 1) * sphereFlux x t u) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t _
      ring
    _ = ∫ t in Ioo a b,
        -(sphereMeasure d).real Set.univ *
          (p t * (t ^ (d - 1) * sphereAverage x t (Δ u))) := hpair
    _ = ∫ t in Ioo a b,
        -((sphereMeasure d).real Set.univ *
          (t ^ (d - 1) * sphereAverage x t (Δ u)) *
            ψ (PDE.scalarToVecOne t)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t _
      dsimp only [p, PDE.scalarPullbackOne]
      ring

/-- Exact Green identity on a positive annulus. -/
theorem weightedSphereFlux_sub_eq_intervalIntegral_laplacianProfile [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) (x : 𝔼) {R a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbR : b < R) :
    b ^ (d - 1) * sphereFlux x b u -
        a ^ (d - 1) * sphereFlux x a u =
      ∫ t in a..b, (sphereMeasure d).real Set.univ *
        (t ^ (d - 1) * sphereAverage x t (Δ u)) := by
  let F : ℝ → ℝ := fun t => t ^ (d - 1) * sphereFlux x t u
  let Q : ℝ → ℝ := fun t => (sphereMeasure d).real Set.univ *
    (t ^ (d - 1) * sphereAverage x t (Δ u))
  have hF : Continuous F :=
    (continuous_pow _).mul (continuous_sphereFlux (hu.of_le (by norm_num)) x)
  have hΔ : Continuous (Δ u) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    have hiter : Continuous (iteratedFDeriv ℝ 2 u) :=
      hu.continuous_iteratedFDeriv (by norm_num)
    fun_prop
  have hQ : Continuous Q := continuous_const.mul
    ((continuous_pow _).mul (continuous_sphereAverage hΔ x))
  have memLp_restrict_Icc_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
      MemLp f 2 (volume.restrict (Icc a b)) := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable.restrict M
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with t ht
    exact hM t ht
  have hFLpClosed := memLp_restrict_Icc_of_continuous F hF
  have hFLp : MemLp F 2 (volume.restrict (Ioo a b)) :=
    hFLpClosed.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hQLp := memLp_restrict_Icc_of_continuous Q hQ
  have hweak : PDE.HasWeakDerivOnIoo a b F Q :=
    weightedSphereFlux_hasWeakDerivOnIoo hu x ha hab hbR
  have hinc := PDE.ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
    hab hF.continuousOn hFLp hQLp hweak
    (show a ∈ Icc a b from left_mem_Icc.2 hab.le)
    (show b ∈ Icc a b from right_mem_Icc.2 hab.le)
  exact hinc

end

end PDE.Internal
