module

public import EllipticRegularity.Ch4.Spagnolo.Polar
public import EllipticRegularity.Ch4.Spagnolo.MatrixInequality
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The Wirtinger inequality on circles, integrated in the radius

For a globally smooth `v : Vec 2 → ℝ`, the restriction of `v` to the circle of
radius `ρ` is a smooth `2π`-periodic function of the angle whose derivative is
the tangential derivative `x⊥ · ∇v`. The Wirtinger inequality (Lemma 4.23, taken as the explicit hypothesis `WirtingerStatement`) on every
circle, integrated in polar coordinates against a nonnegative radial weight,
gives
`∫_{B₁} k(|x|²) (v - c_v(|x|))² ≤ ∫_{B₁} k(|x|²) (x⊥ · ∇v)²`,
where `c_v(ρ)` is the mean of `v` on the circle of radius `ρ`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set

/-- The statement of the Wirtinger inequality (Lemma 4.23), verbatim
the conclusion of the statement `PDE.wirtinger_inequality`. -/
abbrev WirtingerStatement : Prop :=
  ∀ w : ℝ → ℝ, Function.Periodic w (2 * Real.pi) →
    AbsolutelyContinuousOnInterval w 0 (2 * Real.pi) →
    MemLp (deriv w) 2 (volume.restrict (Set.Icc 0 (2 * Real.pi))) →
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (w θ - (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t) ^ 2 ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (deriv w θ) ^ 2

/-- The mean of `v` on the circle of radius `ρ` centred at the origin. -/
noncomputable def circleMean (v : Vec 2 → ℝ) (ρ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), v (polarVec ρ t)

theorem continuous_polarVec : Continuous (fun p : ℝ × ℝ => polarVec p.1 p.2) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, polarVec_apply_zero]; fun_prop
  · simp only [Fin.mk_one, Fin.isValue, polarVec_apply_one]; fun_prop

theorem contDiff_polarVec_angle (ρ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun θ => polarVec ρ θ) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simpa [polarVec] using contDiff_const.mul Real.contDiff_cos
  · simpa [polarVec] using contDiff_const.mul Real.contDiff_sin

theorem hasDerivAt_polarVec_angle (ρ θ : ℝ) :
    HasDerivAt (fun θ => polarVec ρ θ)
      (![-(ρ * Real.sin θ), ρ * Real.cos θ] : Vec 2) θ := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa [polarVec] using (Real.hasDerivAt_cos θ).const_mul ρ
  · simpa [polarVec] using (Real.hasDerivAt_sin θ).const_mul ρ

/-- The Euclidean norm of `polarVec ρ θ` is `ρ` for `ρ ≥ 0`. -/
theorem vecEuclideanNorm_polarVec {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    vecEuclideanNorm (polarVec ρ θ) = ρ := by
  rw [vecEuclideanNorm, vecNormSq_polarVec, Real.sqrt_sq hρ]

theorem continuous_circleMean {v : Vec 2 → ℝ} (hv : Continuous v) :
    Continuous (circleMean v) := by
  unfold circleMean
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun ρ t => v (polarVec ρ t)) (hv.comp continuous_polarVec) _ _

/-- The angular derivative of `v` along a circle is the tangential derivative
`x⊥ · ∇v`. -/
theorem hasDerivAt_comp_polarVec {v : Vec 2 → ℝ} (hv : Differentiable ℝ v) (ρ θ : ℝ) :
    HasDerivAt (fun θ => v (polarVec ρ θ))
      (perpDot (polarVec ρ θ) (classicalGradient v (polarVec ρ θ))) θ := by
  have h := (hv (polarVec ρ θ)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_polarVec_angle ρ θ)
  suffices hval : perpDot (polarVec ρ θ) (classicalGradient v (polarVec ρ θ)) =
      fderiv ℝ v (polarVec ρ θ) (![-(ρ * Real.sin θ), ρ * Real.cos θ] : Vec 2) by
    rw [hval]; exact h
  have hvec : (![-(ρ * Real.sin θ), ρ * Real.cos θ] : Vec 2) =
      (-(ρ * Real.sin θ)) • basisVec 0 + (ρ * Real.cos θ) • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  rw [hvec, map_add, map_smul, map_smul]
  simp only [perpDot, classicalGradient, polarVec_apply_zero, polarVec_apply_one,
    smul_eq_mul]
  ring

theorem deriv_comp_polarVec {v : Vec 2 → ℝ} (hv : Differentiable ℝ v) (ρ θ : ℝ) :
    deriv (fun θ => v (polarVec ρ θ)) θ =
      perpDot (polarVec ρ θ) (classicalGradient v (polarVec ρ θ)) :=
  (hasDerivAt_comp_polarVec hv ρ θ).deriv

private theorem intervalIntegral_two_pi_eq_Ioo {f : ℝ → ℝ}
    (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ = ∫ θ in Ioo (-Real.pi) Real.pi, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]

/-- **Wirtinger on one circle.** For a globally smooth `v` and every radius `ρ`,
`∫_{-π}^{π} (v(ρ e(θ)) - c_v(ρ))² dθ ≤ ∫_{-π}^{π} ((x⊥ · ∇v)(ρ e(θ)))² dθ`. -/
theorem circle_wirtinger (hW : WirtingerStatement) {v : Vec 2 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (ρ : ℝ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, (v (polarVec ρ θ) - circleMean v ρ) ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi,
        perpDot (polarVec ρ θ) (classicalGradient v (polarVec ρ θ)) ^ 2 := by
  set w : ℝ → ℝ := fun θ => v (polarVec ρ θ) with hw
  have hdiff : Differentiable ℝ v := hv.differentiable (by simp)
  have hwsmooth : ContDiff ℝ (⊤ : ℕ∞) w := hv.comp (contDiff_polarVec_angle ρ)
  have hper : Function.Periodic w (2 * Real.pi) := by
    intro θ
    simp only [hw, polarVec_add_two_pi]
  have hac : AbsolutelyContinuousOnInterval w 0 (2 * Real.pi) :=
    (hwsmooth.contDiffOn.of_le (by simp)).absolutelyContinuousOnInterval
  have hderivCont : Continuous (deriv w) := hwsmooth.continuous_deriv (by simp)
  have hderivL2 : MemLp (deriv w) 2 (volume.restrict (Icc 0 (2 * Real.pi))) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hderivCont.continuousOn (s := Icc 0 (2 * Real.pi)))
    refine MemLp.of_bound hderivCont.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hC θ hθ
  have hmain := hW w hper hac hderivL2
  have hderiv : ∀ θ, deriv w θ =
      perpDot (polarVec ρ θ) (classicalGradient v (polarVec ρ θ)) :=
    deriv_comp_polarVec hdiff ρ
  have hmean : (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..(2 * Real.pi), w t = circleMean v ρ := rfl
  rw [hmean] at hmain
  have hperL : Function.Periodic (fun θ => (w θ - circleMean v ρ) ^ 2) (2 * Real.pi) := by
    intro θ; simp only [hper θ]
  have hperR : Function.Periodic (fun θ => (deriv w θ) ^ 2) (2 * Real.pi) := by
    intro θ; simp only [hderiv, polarVec_add_two_pi]
  rw [intervalIntegral_two_pi_eq_Ioo hperL, intervalIntegral_two_pi_eq_Ioo hperR] at hmain
  simpa only [hderiv] using hmain

private theorem polarVec_mem_ball_iff {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    polarVec ρ θ ∈ euclideanBall (0 : Vec 2) 1 ↔ ρ < 1 := by
  change vecNormSq (polarVec ρ θ - 0) < 1 ^ 2 ↔ ρ < 1
  rw [sub_zero, vecNormSq_polarVec]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Integrability on the unit disc of a function continuous on the plane. -/
theorem integrableOn_ball_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (euclideanBall (0 : Vec 2) 1) :=
  ((hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Vec 2) 1))).mono_set
    ((euclideanBall_subset_supBall (by norm_num)).trans Metric.ball_subset_closedBall)

/-- The disc integral in polar coordinates, for a function integrable on the
unit disc. -/
theorem setIntegral_ball_eq_polar {f : Vec 2 → ℝ}
    (hf : IntegrableOn f (euclideanBall (0 : Vec 2) 1)) :
    ∫ x in euclideanBall (0 : Vec 2) 1, f x =
      ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        ρ * (euclideanBall (0 : Vec 2) 1).indicator f (polarVec ρ θ) := by
  rw [← integral_indicator (measurableSet_euclideanBall _ _)]
  exact integral_eq_integral_polar
    ((integrable_indicator_iff (measurableSet_euclideanBall _ _)).2 hf)

/-- The angular integral of the polar integrand of an indicator. -/
theorem integral_polar_indicator_ball {f : Vec 2 → ℝ} {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ θ in Ioo (-Real.pi) Real.pi,
        ρ * (euclideanBall (0 : Vec 2) 1).indicator f (polarVec ρ θ) =
      if ρ < 1 then ρ * ∫ θ in Ioo (-Real.pi) Real.pi, f (polarVec ρ θ) else 0 := by
  split_ifs with h1
  · rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [indicator_of_mem ((polarVec_mem_ball_iff hρ θ).2 h1)]
  · have : ∀ θ, (euclideanBall (0 : Vec 2) 1).indicator f (polarVec ρ θ) = 0 := fun θ =>
      indicator_of_notMem (fun hm => h1 ((polarVec_mem_ball_iff hρ θ).1 hm)) _
    simp [this]

/-- **Radially weighted Wirtinger inequality** for a globally smooth `v`:
`∫_{B₁} k(|x|²) (v - c_v(|x|))² ≤ ∫_{B₁} k(|x|²) (x⊥ · ∇v)²` for every continuous
nonnegative `k`. -/
theorem weighted_circle_wirtinger (hW : WirtingerStatement) {v : Vec 2 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ t, 0 ≤ k t) :
    ∫ x in euclideanBall (0 : Vec 2) 1,
        k (vecNormSq x) * (v x - circleMean v (vecEuclideanNorm x)) ^ 2 ≤
      ∫ x in euclideanBall (0 : Vec 2) 1,
        k (vecNormSq x) * perpDot x (classicalGradient v x) ^ 2 := by
  have hvc : Continuous v := hv.continuous
  have hgradc : Continuous (classicalGradient v) := by
    refine continuous_pi fun i => ?_
    exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hnsq : Continuous (fun x : Vec 2 => vecNormSq x) := by
    simp only [vecNormSq, vecDot]; fun_prop
  have hnorm : Continuous (fun x : Vec 2 => vecEuclideanNorm x) := by
    unfold vecEuclideanNorm; exact Real.continuous_sqrt.comp hnsq
  have hperp : Continuous (fun x : Vec 2 => perpDot x (classicalGradient v x)) := by
    unfold perpDot
    exact ((continuous_apply 0).mul ((continuous_apply 1).comp hgradc)).sub
      ((continuous_apply 1).mul ((continuous_apply 0).comp hgradc))
  set F : Vec 2 → ℝ := fun x =>
    k (vecNormSq x) * (v x - circleMean v (vecEuclideanNorm x)) ^ 2 with hF
  set G : Vec 2 → ℝ := fun x => k (vecNormSq x) * perpDot x (classicalGradient v x) ^ 2
    with hG
  have hFc : Continuous F :=
    (hk.comp hnsq).mul ((hvc.sub ((continuous_circleMean hvc).comp hnorm)).pow 2)
  have hGc : Continuous G := (hk.comp hnsq).mul (hperp.pow 2)
  have hFi := integrableOn_ball_of_continuous hFc
  have hGi := integrableOn_ball_of_continuous hGc
  rw [setIntegral_ball_eq_polar hFi, setIntegral_ball_eq_polar hGi]
  have hFr := integrableOn_polar_radial
    ((integrable_indicator_iff (measurableSet_euclideanBall _ _)).2 hFi)
  have hGr := integrableOn_polar_radial
    ((integrable_indicator_iff (measurableSet_euclideanBall _ _)).2 hGi)
  refine setIntegral_mono_on hFr hGr measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  rw [integral_polar_indicator_ball hρ0, integral_polar_indicator_ball hρ0]
  split_ifs with h1
  · refine mul_le_mul_of_nonneg_left ?_ hρ0.le
    have hFθ : ∀ θ, F (polarVec ρ θ) =
        k (ρ ^ 2) * (v (polarVec ρ θ) - circleMean v ρ) ^ 2 := by
      intro θ
      simp only [hF, vecNormSq_polarVec, vecEuclideanNorm_polarVec hρ0.le]
    have hGθ : ∀ θ, G (polarVec ρ θ) =
        k (ρ ^ 2) * perpDot (polarVec ρ θ) (classicalGradient v (polarVec ρ θ)) ^ 2 := by
      intro θ
      simp only [hG, vecNormSq_polarVec]
    simp only [hFθ, hGθ]
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (circle_wirtinger hW hv ρ) (hk0 _)
  · exact le_rfl

end PDE.Ch4Spagnolo
