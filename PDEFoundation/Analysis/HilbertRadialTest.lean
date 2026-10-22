module

public import PDEFoundation.Analysis.HilbertSubmean
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Pulling positive-radius tests back through the square root

Compactly supported smooth tests on a positive radius interval can be written
as smooth functions of the squared radius.  Vanishing near radius zero removes
the apparent singularity of the square root there.
-/

@[expose] public section

namespace PDE.Internal

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

/-- Pull a radial test back from radius to squared radius. -/
def sqrtPullback (p : ℝ → ℝ) : ℝ → ℝ :=
  fun t => p (Real.sqrt t)

theorem sqrtPullback_apply (p : ℝ → ℝ) (t : ℝ) :
    sqrtPullback p t = p (Real.sqrt t) :=
  rfl

/-- A smooth test supported strictly inside a positive interval remains
globally smooth after composition with the square root. -/
theorem contDiff_sqrtPullback_of_tsupport_subset_Ioo
    {p : ℝ → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) {ε r : ℝ} (hε : 0 < ε)
    (hsupp : tsupport p ⊆ Ioo ε r) :
    ContDiff ℝ (⊤ : ℕ∞) (sqrtPullback p) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · exact hp.contDiffAt.comp t (Real.contDiffAt_sqrt ht.ne')
  · have hsqrt_lt : Real.sqrt t < ε := by
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt ht)]
      exact hε
    have hopen : IsOpen {z : ℝ | Real.sqrt z < ε} :=
      isOpen_lt continuous_id.sqrt continuous_const
    have hmem : t ∈ {z : ℝ | Real.sqrt z < ε} := hsqrt_lt
    have hev : sqrtPullback p =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hmem] with z hz
      rw [sqrtPullback_apply]
      apply image_eq_zero_of_notMem_tsupport
      intro hmemsupp
      exact (not_lt_of_ge (hsupp hmemsupp).1.le) hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- On positive radii, pulling back through the square root and evaluating at
the squared radius recovers the original test. -/
@[simp] theorem sqrtPullback_sq {p : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    sqrtPullback p (s ^ 2) = p s := by
  rw [sqrtPullback_apply, Real.sqrt_sq hs]

/-- The radial derivative of the square-root pullback has the exact chain-rule
normalization used by the flux identity. -/
theorem two_mul_mul_deriv_sqrtPullback_sq
    {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p) {s : ℝ} (hs : 0 < s) :
    2 * s * deriv (sqrtPullback p) (s ^ 2) = deriv p s := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
  have hpderiv : HasDerivAt p (deriv p s) s :=
    (hp.differentiable (by norm_num) s).hasDerivAt
  have hsqrt := Real.hasDerivAt_sqrt hs2
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs.le
  have hpderiv' : HasDerivAt p (deriv p s) (Real.sqrt (s ^ 2)) := by
    rwa [hsq]
  have hcomp := hpderiv'.comp (s ^ 2) hsqrt
  have hderiv : deriv (sqrtPullback p) (s ^ 2) =
      deriv p s * (1 / (2 * s)) := by
    change deriv (p ∘ Real.sqrt) (s ^ 2) = _
    rw [hcomp.deriv]
    rw [hsq]
  rw [hderiv]
  field_simp

/-- The pullback vanishes outside the squared support window. -/
theorem sqrtPullback_eq_zero_of_not_mem_sq_window
    {p : ℝ → ℝ} {ε r t : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsupp : tsupport p ⊆ Ioo ε r)
    (ht : t < ε ^ 2 ∨ r ^ 2 < t) :
    sqrtPullback p t = 0 := by
  rw [sqrtPullback_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hwindow := hsupp hmem
  rcases ht with ht | ht
  · exact (not_lt_of_ge hwindow.1.le) ((Real.sqrt_lt' hε).2 ht)
  · have ht0 : 0 ≤ t := le_trans (sq_nonneg r) (le_of_lt ht)
    have hsqrt_lt : r < Real.sqrt t := (Real.lt_sqrt hr.le).2 ht
    exact (not_lt_of_ge hsqrt_lt.le) hwindow.2

/-- The square-root pullback itself has compact support. -/
theorem hasCompactSupport_sqrtPullback_of_tsupport_subset_Ioo
    {p : ℝ → ℝ} {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsupp : tsupport p ⊆ Ioo ε r) :
    HasCompactSupport (sqrtPullback p) := by
  apply HasCompactSupport.intro (K := Icc (ε ^ 2) (r ^ 2)) isCompact_Icc
  intro t ht
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  exact sqrtPullback_eq_zero_of_not_mem_sq_window hε hr hsupp ht

/-- The associated squared-distance radial test is compactly supported, and
its topological support lies in any strictly larger ball. -/
theorem radial_sqrtPullback_hasCompactSupport_and_tsupport_subset_ball
    {p : ℝ → ℝ} {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrR : r < R)
    (hsupp : tsupport p ⊆ Ioo ε r) (x : HilbertVec d) :
    HasCompactSupport
        (fun y : HilbertVec d => sqrtPullback p (‖y - x‖ ^ 2)) ∧
      tsupport (fun y : HilbertVec d => sqrtPullback p (‖y - x‖ ^ 2)) ⊆
        Metric.ball x R := by
  let ψ : HilbertVec d → ℝ :=
    fun y => sqrtPullback p (‖y - x‖ ^ 2)
  have hsupport : Function.support ψ ⊆ Metric.closedBall x r := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hnot
    have hnorm : r < ‖y - x‖ := lt_of_not_ge hnot
    have hsquare : r ^ 2 < ‖y - x‖ ^ 2 := by
      nlinarith only [hr, hnorm, norm_nonneg (y - x)]
    have hzero : ψ y = 0 :=
      sqrtPullback_eq_zero_of_not_mem_sq_window hε hr hsupp (Or.inr hsquare)
    exact (Function.mem_support.mp hy) hzero
  have hcompact : HasCompactSupport ψ :=
    (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport ψ)
      (closure_minimal hsupport isClosed_closedBall)
  refine ⟨hcompact, ?_⟩
  exact (closure_minimal hsupport isClosed_closedBall).trans
    (Metric.closedBall_subset_ball hrR)

end

end PDE.Internal
