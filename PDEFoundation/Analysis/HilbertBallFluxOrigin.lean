module

public import PDEFoundation.Analysis.HilbertBallFlux
public import PDEFoundation.Analysis.HilbertBallAverage

/-! # The ball-flux identity including the origin -/

@[expose] public section

namespace PDE.Internal

open scoped Topology
open scoped Laplacian
open MeasureTheory Metric Set InnerProductSpace Filter

noncomputable section

variable {d : ℕ}

local notation "𝔼" => HilbertVec d

/-- The annular Green identity extends to the origin in dimensions at least
two; the factor `r^(d-1)` kills the finite flux at radius zero. -/
theorem weightedSphereFlux_eq_integral_laplacianProfile_of_two_le
    [NeZero d] (hd : 2 ≤ d) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u)
    (x : 𝔼) {R r : ℝ} (hr : 0 < r) (hrR : r < R) :
    r ^ (d - 1) * sphereFlux x r u =
      ∫ t in (0 : ℝ)..r, (sphereMeasure d).real Set.univ *
        (t ^ (d - 1) * sphereAverage x t (Δ u)) := by
  let F : ℝ → ℝ := fun t => t ^ (d - 1) * sphereFlux x t u
  let Q : ℝ → ℝ := fun t => (sphereMeasure d).real Set.univ *
    (t ^ (d - 1) * sphereAverage x t (Δ u))
  let P : ℝ → ℝ := PDE.intervalPrimitive 0 Q
  let G : ℝ → ℝ := fun t => F t - P t
  have hF : Continuous F :=
    (continuous_pow _).mul (continuous_sphereFlux (hu.of_le (by norm_num)) x)
  have hΔ : Continuous (Δ u) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    have hiter : Continuous (iteratedFDeriv ℝ 2 u) :=
      hu.continuous_iteratedFDeriv (by norm_num)
    fun_prop
  have hQ : Continuous Q := continuous_const.mul
    ((continuous_pow _).mul (continuous_sphereAverage hΔ x))
  have hP : Continuous P := by
    exact (intervalIntegral.differentiable_integral_of_continuous hQ).continuous
  have hG : Continuous G := hF.sub hP
  have hconst : G r = G 0 := by
    have hev : G =ᶠ[𝓝[>] (0 : ℝ)] fun _ => G r := by
      have hmem : Ioo (0 : ℝ) r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
      filter_upwards [hmem] with a ha
      have hgreen := weightedSphereFlux_sub_eq_intervalIntegral_laplacianProfile
        hu x ha.1 ha.2 hrR
      have hQint : IntegrableOn Q (Icc 0 r) :=
        hQ.continuousOn.integrableOn_compact isCompact_Icc
      have hprim : P r - P a = ∫ t in a..r, Q t :=
        PDE.intervalPrimitive_sub_eq_intervalIntegral hQint
          (show a ∈ Icc 0 r from ⟨ha.1.le, ha.2.le⟩)
          (show r ∈ Icc 0 r from right_mem_Icc.2 hr.le)
      dsimp only [G, F, Q] at hgreen ⊢
      dsimp only [P]
      linarith only [hgreen, hprim]
    have hright : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G r)) :=
      Tendsto.congr' hev.symm tendsto_const_nhds
    have hzero : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) :=
      hG.continuousAt.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hright hzero
  have hdsub : d - 1 ≠ 0 := by omega
  have hF0 : F 0 = 0 := by simp [F, hdsub]
  have hP0 : P 0 = 0 := by simp [P]
  dsimp only [G] at hconst
  rw [hF0, hP0, sub_zero] at hconst
  have heq : F r = P r := sub_eq_zero.mp hconst
  simpa only [F, P, Q, PDE.intervalPrimitive] using heq

/-- Green's identity on a ball, in the weighted form that avoids negative
powers of the radius. -/
theorem weightedSphereFlux_eq_integral_ball_laplacian_of_two_le
    [NeZero d] (hd : 2 ≤ d) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u)
    (x : 𝔼) {R r : ℝ} (hr : 0 < r) (hrR : r < R) :
    r ^ (d - 1) * sphereFlux x r u =
      ∫ y in Metric.ball x r, Δ u y := by
  rw [weightedSphereFlux_eq_integral_laplacianProfile_of_two_le hd hu x hr hrR]
  have hΔ : Continuous (Δ u) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    have hiter : Continuous (iteratedFDeriv ℝ 2 u) :=
      hu.continuous_iteratedFDeriv (by norm_num)
    fun_prop
  have hpolar := integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage hΔ x hr
  calc
    (∫ t in (0 : ℝ)..r, (sphereMeasure d).real Set.univ *
        (t ^ (d - 1) * sphereAverage x t (Δ u))) =
        (sphereMeasure d).real Set.univ *
          ∫ t in (0 : ℝ)..r, t ^ (d - 1) * sphereAverage x t (Δ u) := by
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ y in Metric.ball x r, Δ u y := hpolar.symm

/-- The radial derivative of a spherical average equals `r / d` times the
volume-normalized ball average of the Laplacian. -/
theorem hasDerivAt_sphereAverage_eq_r_div_dim_mul_ballAverage_laplacian_of_two_le
    [NeZero d] (hd : 2 ≤ d) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u)
    (x : 𝔼) {R r : ℝ} (hr : 0 < r) (hrR : r < R) :
    HasDerivAt (fun s => sphereAverage x s u)
      ((r / d) * ((volume (Metric.ball x r)).toReal⁻¹ *
        ∫ y in Metric.ball x r, Δ u y)) r := by
  have hderiv := hasDerivAt_sphereAverage (hu.of_le (by norm_num)) x r
  rw [← sphereFlux_def, smul_eq_mul] at hderiv
  have hflux := weightedSphereFlux_eq_integral_ball_laplacian_of_two_le
    hd hu x hr hrR
  have hvol := volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div x hr
  have hσ : (sphereMeasure d).real Set.univ ≠ 0 :=
    sphereMeasure_real_univ_ne_zero
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hr0 : r ≠ 0 := hr.ne'
  have hrpow : r ^ (d - 1) ≠ 0 := pow_ne_zero _ hr0
  have hpow : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  apply hderiv.congr_deriv
  rw [hvol]
  field_simp
  rw [hpow, ← hflux]
  ring

end

end PDE.Internal
