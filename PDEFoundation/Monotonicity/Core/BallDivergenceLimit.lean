module

public import PDEFoundation.Monotonicity.Core.BallDivergenceTest
public import PDEFoundation.Monotonicity.Core.BallDivergencePolar
public import PDEFoundation.Analysis.HilbertSubmean

/-!
# The divergence theorem on balls for globally `C¹` fields

Let `F : Vec d → Vec d` be `C¹` and `0 < r`.  Testing with the radial profile `radialDrop a r`
and letting `a ↑ r` yields
`∫_{B_r} div F = r⁻¹ ∫_{∂B_r} F · x`.  The right side is read off by polar coordinates and an
approximate identity in the radius; no continuity at the origin is needed, so the argument works
for every `d ≥ 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE.BallDivergence

noncomputable section

variable {d : ℕ}

theorem euclideanSqDist_zero_right (x : Vec d) : euclideanSqDist x 0 = vecNormSq x := by
  simp [euclideanSqDist]

/-- `sphereIntegral` about `0` in terms of the Hilbert spherical average. -/
theorem sphereIntegral_zero_eq [NeZero d] (g : Vec d → ℝ) (s : ℝ) :
    sphereIntegral (0 : Vec d) s g =
      s ^ (d - 1) * ((Internal.sphereMeasure d).real univ *
        Internal.sphereAverage (0 : HilbertVec d) s (fun y => g y.toVec)) := by
  have h := Internal.integral_sphere_eq_measureReal_smul_sphereAverage
    (fun y : HilbertVec d => g y.toVec) 0 s
  have e : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
      g ((0 : Vec d) + s • (ω : HilbertVec d).toVec) =
        (fun y : HilbertVec d => g y.toVec) (0 + s • (ω : HilbertVec d)) := by
    intro ω; show _ = g ((0 + s • (ω : HilbertVec d)).toVec); congr 1
  unfold sphereIntegral
  have h2 : (∫ ω : Metric.sphere (0 : HilbertVec d) 1,
      g ((0 : Vec d) + s • (ω : HilbertVec d).toVec) ∂(Internal.sphereMeasure d)) =
      ∫ ω : Metric.sphere (0 : HilbertVec d) 1,
        (fun y : HilbertVec d => g y.toVec) (0 + s • (ω : HilbertVec d))
          ∂(Internal.sphereMeasure d) :=
    integral_congr_ae (Filter.Eventually.of_forall e)
  rw [smul_eq_mul] at h
  rw [← h]
  exact congrArg _ h2

theorem continuous_sphereIntegral_zero [NeZero d] {g : Vec d → ℝ} (hg : Continuous g) :
    Continuous (fun s : ℝ => sphereIntegral (0 : Vec d) s g) := by
  have : (fun s : ℝ => sphereIntegral (0 : Vec d) s g) = fun s =>
      s ^ (d - 1) * ((Internal.sphereMeasure d).real univ *
        Internal.sphereAverage (0 : HilbertVec d) s (fun y => g y.toVec)) :=
    funext (sphereIntegral_zero_eq g)
  rw [this]
  exact (continuous_pow _).mul (continuous_const.mul
    (Internal.continuous_sphereAverage (hg.comp continuous_toVec) 0))

/-- The weight of the radial approximate identity. -/
def radialWeight (a r s : ℝ) : ℝ := -(2 * s * deriv (radialDrop a r) (s ^ 2))

theorem continuous_radialWeight (a r : ℝ) : Continuous (radialWeight a r) := by
  unfold radialWeight
  exact (((continuous_const.mul continuous_id).mul
    (((contDiff_radialDrop a r).continuous_deriv (by simp)).comp (continuous_pow 2)))).neg

theorem radialWeight_nonneg {a r s : ℝ} (ha : 0 < a) (har : a < r) (hs : 0 ≤ s) :
    0 ≤ radialWeight a r s := by
  unfold radialWeight
  have := deriv_radialDrop_nonpos ha har (s ^ 2)
  nlinarith only [this, hs]

theorem radialWeight_eq_zero_of_lt {a r s : ℝ} (ha : 0 < a) (har : a < r) (hs : 0 < s)
    (hsa : s < a) : radialWeight a r s = 0 := by
  unfold radialWeight
  rw [deriv_radialDrop_eq_zero_of_lt ha har (by nlinarith only [hs, hsa])]
  simp

theorem radialWeight_eq_zero_of_gt {a r s : ℝ} (ha : 0 < a) (har : a < r) (hs : r < s) :
    radialWeight a r s = 0 := by
  unfold radialWeight
  rw [deriv_radialDrop_eq_zero_of_gt ha har (by nlinarith only [ha, har, hs])]
  simp

theorem hasCompactSupport_radialWeight {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HasCompactSupport (radialWeight a r) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r))
  intro s hs
  unfold radialWeight
  rw [deriv_radialDrop_eq_zero_of_gt ha har (by
    rcases not_and_or.1 (mem_Icc.not.1 hs) with h | h
    · nlinarith only [h, ha, har]
    · nlinarith only [h, ha, har])]
  simp

theorem integral_radialWeight {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∫ s in Ioi (0 : ℝ), radialWeight a r s = 1 := by
  have hr : 0 < r := ha.trans har
  have hz : ∀ s ∈ Ioi (0 : ℝ) \ Ioc 0 r, radialWeight a r s = 0 := by
    intro s hs
    exact radialWeight_eq_zero_of_gt ha har (not_le.1 (fun h => hs.2 ⟨hs.1, h⟩))
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self hz,
    ← intervalIntegral.integral_of_le hr.le]
  have hder : ∀ s ∈ uIcc (0 : ℝ) r,
      HasDerivAt (fun s => -(radialDrop a r (s ^ 2))) (radialWeight a r s) s := by
    intro s _
    have hχ : HasDerivAt (radialDrop a r) (deriv (radialDrop a r) (s ^ 2)) (s ^ 2) :=
      (((contDiff_radialDrop a r).differentiable (by simp)) _).hasDerivAt
    have hc : HasDerivAt (fun s : ℝ => -(radialDrop a r (s ^ 2)))
        (-(deriv (radialDrop a r) (s ^ 2) * (((2 : ℕ) : ℝ) * s ^ (2 - 1)))) s :=
      (HasDerivAt.comp (h := fun x : ℝ => x ^ 2) s hχ (hasDerivAt_pow 2 s)).neg
    refine hc.congr_deriv ?_
    unfold radialWeight
    simp only [Nat.cast_ofNat]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((continuous_radialWeight a r).intervalIntegrable _ _)]
  rw [radialDrop_eq_zero ha har (le_refl _), radialDrop_eq_one ha har (by nlinarith only [ha])]
  norm_num

/-- Continuity of the classical divergence of a `C¹` field. -/
theorem continuous_classicalDivergence {F : Vec d → Vec d} (hF : ContDiff ℝ 1 F) :
    Continuous (classicalDivergence F) := by
  unfold classicalDivergence
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : ContDiff ℝ 1 (fun y => F y k) := contDiff_pi.1 hF k
  exact (hk.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Exact identity at a radius `a < r`, written with the radial approximate-identity weight. -/
theorem integral_classicalDivergence_mul_radialDrop_eq [NeZero d] {F : Vec d → Vec d}
    (hF : ContDiff ℝ 1 F) {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∫ x, classicalDivergence F x * radialDrop a r (vecNormSq x) =
      ∫ s in Ioi (0 : ℝ), radialWeight a r s *
        (sphereIntegral (0 : Vec d) s (fun x => vecDot (F x) x) / s) := by
  have hr : 0 < r := ha.trans har
  have hgc : Continuous (fun x => vecDot (F x) x) := by
    unfold vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hF.continuous).mul (continuous_apply i)
  rw [integral_classicalDivergence_mul_radialDrop hF ha har]
  have hpolar := integral_radial_mul_eq_integral_Ioi_sphereIntegral hgc
    (c := fun t => 2 * deriv (radialDrop a r) t)
    (continuous_const.mul ((contDiff_radialDrop a r).continuous_deriv (by simp))) hr.le
    (fun t ht => by
      simp only [deriv_radialDrop_eq_zero_of_gt ha har ht, mul_zero])
  have hpolar' : ∫ x, 2 * deriv (radialDrop a r) (vecNormSq x) * vecDot (F x) x =
      ∫ s in Ioi (0 : ℝ), 2 * deriv (radialDrop a r) (s ^ 2) *
        sphereIntegral (0 : Vec d) s (fun x => vecDot (F x) x) := hpolar
  rw [hpolar', ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : s ≠ 0 := (ne_of_gt hs)
  simp only [radialWeight]
  field_simp

/-- The right side of the exact identity tends to the flux density at radius `r`. -/
theorem tendsto_integral_radialWeight_mul {W : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hWc : ContinuousOn W (Ioi 0)) :
    Tendsto (fun a => ∫ s in Ioi (0 : ℝ), radialWeight a r s * W s) (𝓝[<] r) (𝓝 (W r)) := by
  have hW : ContinuousAt W r := hWc.continuousAt (Ioi_mem_nhds hr)
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨η, hη, hηW⟩ := Metric.continuousAt_iff.1 hW (δ / 2) (by linarith only [hδ])
  have hev : Ioo (max (r - η) (r / 2)) r ∈ 𝓝[<] r :=
    Ioo_mem_nhdsLT (max_lt (by linarith only [hη]) (by linarith only [hr]))
  filter_upwards [hev] with a ha
  have hr2 : r / 2 < a := lt_of_le_of_lt (le_max_right _ _) ha.1
  have ha0 : 0 < a := by linarith only [hr2, hr]
  have har : a < r := ha.2
  have hint : Integrable (radialWeight a r) :=
    (continuous_radialWeight a r).integrable_of_hasCompactSupport
      (hasCompactSupport_radialWeight ha0 har)
  have hint1 := hint.integrableOn (s := Ioi (0 : ℝ))
  have hbound : ∀ s ∈ Ioi (0 : ℝ),
      ‖radialWeight a r s * (W s - W r)‖ ≤ δ / 2 * radialWeight a r s := by
    intro s hs
    have hs0 : 0 < s := hs
    by_cases hsa : s < a
    · rw [radialWeight_eq_zero_of_lt ha0 har hs0 hsa]; simp
    by_cases hsr : r < s
    · rw [radialWeight_eq_zero_of_gt ha0 har hsr]; simp
    have hdist : dist s r < η := by
      rw [Real.dist_eq, abs_lt]
      have h1 : r - η < a := lt_of_le_of_lt (le_max_left _ _) ha.1
      constructor <;> linarith only [not_lt.1 hsa, not_lt.1 hsr, h1, har]
    have hw := radialWeight_nonneg ha0 har hs0.le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, mul_comm]
    have := le_of_lt (hηW hdist)
    rw [Real.dist_eq] at this
    exact mul_le_mul_of_nonneg_right this hw
  have hWint : IntegrableOn (fun s => radialWeight a r s * W s) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun s => radialWeight a r s * W s) (Icc a r) :=
      ((continuous_radialWeight a r).continuousOn.mul
        (hWc.mono (fun s hs => lt_of_lt_of_le ha0 hs.1))).integrableOn_Icc
    refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs.1
    have : radialWeight a r s = 0 := by
      by_cases hsa : s < a
      · exact radialWeight_eq_zero_of_lt ha0 har hs0 hsa
      · exact radialWeight_eq_zero_of_gt ha0 har
          (not_le.1 fun h => hs.2 ⟨not_lt.1 hsa, h⟩)
    rw [this, zero_mul]
  have hdiff : ∫ s in Ioi (0 : ℝ), radialWeight a r s * (W s - W r) =
      (∫ s in Ioi (0 : ℝ), radialWeight a r s * W s) - W r := by
    have h1 : ∀ s, radialWeight a r s * (W s - W r) =
        radialWeight a r s * W s - radialWeight a r s * W r := fun s => by ring
    simp_rw [h1]
    rw [integral_sub hWint (hint1.mul_const _), integral_mul_const, integral_radialWeight ha0 har,
      one_mul]
  have hle : ‖∫ s in Ioi (0 : ℝ), radialWeight a r s * (W s - W r)‖ ≤ δ / 2 := by
    have := norm_integral_le_of_norm_le (hint1.const_mul (δ / 2))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound))
    rw [integral_const_mul, integral_radialWeight ha0 har, mul_one] at this
    exact this
  rw [hdiff] at hle
  rw [Real.dist_eq]
  have := lt_of_le_of_lt hle (half_lt_self hδ)
  rwa [Real.norm_eq_abs] at this

/-- The left side of the exact identity tends to the integral over the open ball. -/
theorem tendsto_integral_divergence_mul_radialDrop {F : Vec d → Vec d} (hF : ContDiff ℝ 1 F)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun a => ∫ x, classicalDivergence F x * radialDrop a r (vecNormSq x)) (𝓝[<] r)
      (𝓝 (∫ x in euclideanBall (0 : Vec d) r, classicalDivergence F x)) := by
  have hdc := continuous_classicalDivergence hF
  have hmem : ∀ x : Vec d, x ∈ euclideanBall (0 : Vec d) r ↔ vecNormSq x < r ^ 2 := by
    intro x; unfold euclideanBall; simp only [mem_ofPred_eq, euclideanSqDist_zero_right]
  have hcl : ∀ x : Vec d, x ∈ euclideanClosedBall (0 : Vec d) r ↔ vecNormSq x ≤ r ^ 2 := by
    intro x; unfold euclideanClosedBall; simp only [mem_ofPred_eq, euclideanSqDist_zero_right]
  rw [← integral_indicator (measurableSet_euclideanBall (0 : Vec d) r)]
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := (euclideanClosedBall (0 : Vec d) r).indicator fun x => |classicalDivergence F x|)
    ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun a => ?_
    exact (hdc.mul ((contDiff_radialDrop a r).continuous.comp
      contDiff_vecNormSq.continuous)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT hr] with a ha
    refine Filter.Eventually.of_forall fun x => ?_
    have ha0 : 0 < a := ha.1
    by_cases hx : x ∈ euclideanClosedBall (0 : Vec d) r
    · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (radialDrop_nonneg a r _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (radialDrop_le_one a r _)
    · rw [indicator_of_notMem hx]
      rw [hcl, not_le] at hx
      rw [radialDrop_eq_zero ha0 ha.2 hx.le]; simp
  · exact ((hdc.abs.continuousOn.integrableOn_compact
      (isCompact_euclideanClosedBall (0 : Vec d) hr.le))).integrable_indicator
      (measurableSet_euclideanClosedBall (0 : Vec d) r)
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ euclideanBall (0 : Vec d) r
    · rw [indicator_of_mem hx]
      have hx' := (hmem x).1 hx
      have hsq : Real.sqrt (vecNormSq x) < r := by
        rw [Real.sqrt_lt' hr]; exact hx'
      have hev : Ioo (Real.sqrt (vecNormSq x)) r ∈ 𝓝[<] r := Ioo_mem_nhdsLT hsq
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with a ha
      have ha0 : 0 < a := lt_of_le_of_lt (Real.sqrt_nonneg _) ha.1
      rw [radialDrop_eq_one ha0 ha.2 ?_, mul_one]
      calc vecNormSq x = Real.sqrt (vecNormSq x) ^ 2 :=
            (Real.sq_sqrt (vecNormSq_nonneg x)).symm
        _ ≤ a ^ 2 := by
            have := Real.sqrt_nonneg (vecNormSq x)
            nlinarith only [ha.1, this]
    · rw [indicator_of_notMem hx]
      have hx' : r ^ 2 ≤ vecNormSq x := not_lt.1 (fun h => hx ((hmem x).2 h))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hr] with a ha
      rw [radialDrop_eq_zero ha.1 ha.2 hx', mul_zero]

/-- The divergence theorem on a ball for a globally `C¹` field. -/
theorem integral_euclideanBall_classicalDivergence_of_contDiff [NeZero d] {F : Vec d → Vec d}
    (hF : ContDiff ℝ 1 F) {r : ℝ} (hr : 0 < r) :
    ∫ x in euclideanBall (0 : Vec d) r, classicalDivergence F x =
      r⁻¹ * sphereIntegral (0 : Vec d) r (fun x => vecDot (F x) x) := by
  have hgc : Continuous (fun x => vecDot (F x) x) := by
    unfold vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hF.continuous).mul (continuous_apply i)
  set S : ℝ → ℝ := fun s => sphereIntegral (0 : Vec d) s (fun x => vecDot (F x) x) with hS
  have hSc : Continuous S := continuous_sphereIntegral_zero hgc
  have hWc : ContinuousOn (fun s => S s / s) (Ioi 0) :=
    hSc.continuousOn.div continuousOn_id (fun s hs => ne_of_gt hs)
  have h1 := tendsto_integral_divergence_mul_radialDrop hF hr
  have h2 := tendsto_integral_radialWeight_mul hr hWc
  have h3 : (fun a => ∫ x, classicalDivergence F x * radialDrop a r (vecNormSq x)) =ᶠ[𝓝[<] r]
      fun a => ∫ s in Ioi (0 : ℝ), radialWeight a r s * (S s / s) := by
    filter_upwards [Ioo_mem_nhdsLT hr] with a ha
    exact integral_classicalDivergence_mul_radialDrop_eq hF ha.1 ha.2
  have h4 := tendsto_nhds_unique (h1.congr' h3) h2
  rw [h4, div_eq_inv_mul]
