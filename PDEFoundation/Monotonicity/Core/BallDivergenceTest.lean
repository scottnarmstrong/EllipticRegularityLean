module

public import PDEFoundation.Analysis.LocalDivergenceIBP
public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Radial test functions for the divergence theorem on balls

For `0 < a < r` the profile `radialDrop a r` is a smooth function of the squared radius which is
`1` on `t ≤ a²` and `0` on `t ≥ r²`.  The test function `x ↦ radialDrop a r (|x|²)` is a smooth
compactly supported test, and the whole-space integration by parts for a `C¹` field `F` gives

`∫ div F · radialDrop(|x|²) = -∫ 2 radialDrop'(|x|²) (F · x)`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.BallDivergence

noncomputable section

/-- Smooth monotone drop from `1` to `0` as the squared radius runs over `[a², r²]`. -/
def radialDrop (a r t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t - a ^ 2) / (r ^ 2 - a ^ 2))

theorem contDiff_radialDrop (a r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (radialDrop a r) := by
  unfold radialDrop
  exact contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))

theorem radialDrop_eq_one {a r t : ℝ} (ha : 0 < a) (har : a < r) (ht : t ≤ a ^ 2) :
    radialDrop a r t = 1 := by
  have hpos : 0 < r ^ 2 - a ^ 2 := by nlinarith only [ha, har]
  unfold radialDrop
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith only [ht]) hpos.le)]
  norm_num

theorem radialDrop_eq_zero {a r t : ℝ} (ha : 0 < a) (har : a < r) (ht : r ^ 2 ≤ t) :
    radialDrop a r t = 0 := by
  have hpos : 0 < r ^ 2 - a ^ 2 := by nlinarith only [ha, har]
  unfold radialDrop
  rw [Real.smoothTransition.one_of_one_le
    ((one_le_div hpos).2 (by linarith only [ht]))]
  norm_num

theorem radialDrop_antitone {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Antitone (radialDrop a r) := by
  have hpos : 0 < r ^ 2 - a ^ 2 := by nlinarith only [ha, har]
  intro s t hst
  unfold radialDrop
  have : (s - a ^ 2) / (r ^ 2 - a ^ 2) ≤ (t - a ^ 2) / (r ^ 2 - a ^ 2) :=
    div_le_div_of_nonneg_right (by linarith only [hst]) hpos.le
  linarith only [Real.smoothTransition.monotone this]

theorem deriv_radialDrop_nonpos {a r : ℝ} (ha : 0 < a) (har : a < r) (t : ℝ) :
    deriv (radialDrop a r) t ≤ 0 :=
  (radialDrop_antitone ha har).deriv_nonpos

theorem radialDrop_nonneg (a r t : ℝ) :
    0 ≤ radialDrop a r t := by
  unfold radialDrop
  linarith only [Real.smoothTransition.le_one ((t - a ^ 2) / (r ^ 2 - a ^ 2))]

theorem radialDrop_le_one (a r t : ℝ) :
    radialDrop a r t ≤ 1 := by
  unfold radialDrop
  linarith only [Real.smoothTransition.nonneg ((t - a ^ 2) / (r ^ 2 - a ^ 2))]

theorem deriv_radialDrop_eq_zero_of_lt {a r t : ℝ} (ha : 0 < a) (har : a < r) (ht : t < a ^ 2) :
    deriv (radialDrop a r) t = 0 := by
  have hev : radialDrop a r =ᶠ[nhds t] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact radialDrop_eq_one ha har (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

theorem deriv_radialDrop_eq_zero_of_gt {a r t : ℝ} (ha : 0 < a) (har : a < r) (ht : r ^ 2 < t) :
    deriv (radialDrop a r) t = 0 := by
  have hev : radialDrop a r =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact radialDrop_eq_zero ha har (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

/-- The coordinate derivative of the squared norm. -/
theorem fderiv_vecNormSq_basisVec {d : ℕ} (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y : Vec d => vecNormSq y) x (basisVec i) = 2 * x i := by
  have h : HasFDerivAt (fun y : Vec d => ∑ j, y j * y j)
      (∑ j, (x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
        x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))) x :=
    HasFDerivAt.fun_sum (fun j _ => (hasFDerivAt_apply j x).mul (hasFDerivAt_apply j x))
  have hq : (fun y : Vec d => vecNormSq y) = fun y : Vec d => ∑ j, y j * y j := rfl
  rw [hq, h.fderiv]
  simp only [sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, basisVec,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib]
  simp [two_mul]

/-- The radial test function of squared radius, as a bundled whole-space test. -/
def radialTest {d : ℕ} {a r : ℝ} (ha : 0 < a) (har : a < r) :
    WeakTestFunction (Set.univ : Set (Vec d)) where
  toFun := fun x => radialDrop a r (vecNormSq x)
  contDiff := (contDiff_radialDrop a r).comp contDiff_vecNormSq
  hasCompactSupport := by
    apply HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) (ha.trans har).le)
    intro x hx
    apply radialDrop_eq_zero ha har
    have hx' : r ^ 2 < euclideanSqDist x 0 := not_le.1 hx
    have : euclideanSqDist x 0 = vecNormSq x := by simp [euclideanSqDist]
    linarith only [hx', this]
  tsupport_subset := subset_univ _

theorem radialTest_partialDeriv {d : ℕ} {a r : ℝ} (ha : 0 < a) (har : a < r) (x : Vec d)
    (i : Fin d) :
    (radialTest ha har).partialDeriv i x =
      deriv (radialDrop a r) (vecNormSq x) * (2 * x i) := by
  have hχ : HasDerivAt (radialDrop a r) (deriv (radialDrop a r) (vecNormSq x)) (vecNormSq x) :=
    (((contDiff_radialDrop a r).differentiable (by simp)) _).hasDerivAt
  have hq : HasFDerivAt (fun y : Vec d => vecNormSq y)
      (fderiv ℝ (fun y : Vec d => vecNormSq y) x) x :=
    ((contDiff_vecNormSq.differentiable (by simp)) x).hasFDerivAt
  have hc := hχ.comp_hasFDerivAt x hq
  unfold WeakTestFunction.partialDeriv
  change (fderiv ℝ (radialDrop a r ∘ fun y : Vec d => vecNormSq y) x) (basisVec i) = _
  rw [hc.fderiv]
  simp only [smul_apply, smul_eq_mul, fderiv_vecNormSq_basisVec]

/-- Whole-space integration by parts against the radial test. -/
theorem integral_classicalDivergence_mul_radialDrop {d : ℕ} {F : Vec d → Vec d}
    (hF : ContDiff ℝ 1 F) {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∫ x, classicalDivergence F x * radialDrop a r (vecNormSq x) =
      -∫ x, 2 * deriv (radialDrop a r) (vecNormSq x) * vecDot (F x) x := by
  have hJ : ∀ i, ContDiffOn ℝ 1 (fun x => F x i) (Set.univ : Set (Vec d)) :=
    fun i => ((contDiff_pi.1 hF) i).contDiffOn
  have h := integral_vecDot_weakTestFunction_grad_eq_neg_integral_divergence_mul
    isOpen_univ F hJ (radialTest ha har)
  simp only [Measure.restrict_univ] at h
  have hl : (∫ x, vecDot (F x) ((radialTest ha har).grad x)) =
      ∫ x, 2 * deriv (radialDrop a r) (vecNormSq x) * vecDot (F x) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot, WeakTestFunction.grad_apply, radialTest_partialDeriv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hr : (∫ x, (∑ i : Fin d, classicalGradient (fun y => F y i) x i) *
      (radialTest ha har) x) =
      ∫ x, classicalDivergence F x * radialDrop a r (vecNormSq x) := rfl
  rw [hl, hr] at h
  linarith only [h]

end

end PDE.BallDivergence
