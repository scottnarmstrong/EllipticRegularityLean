module

public import EllipticRegularity.Parabolic.Energy.Mollifier

/-!
# The test functions `y ↦ k_a(x - y)`
-/

@[expose] public section

namespace PDE.Parabolic.Energy

open MeasureTheory Set Metric

variable {d : ℕ}

/-- The translated, reflected kernel used as a test function. -/
noncomputable def zeta (a : ℝ) (x : Vec d) : Vec d → ℝ := fun y => kern a (x - y)

theorem zeta_contDiff (a : ℝ) (x : Vec d) : ContDiff ℝ (⊤ : ℕ∞) (zeta a x) :=
  (kern_smooth a).comp (contDiff_const.sub contDiff_id)

theorem zeta_contDiff_one (a : ℝ) (x : Vec d) : ContDiff ℝ 1 (zeta a x) :=
  (zeta_contDiff a x).of_le (by exact_mod_cast le_top)

theorem zeta_eq_zero {a : ℝ} (ha : 0 < a) {x y : Vec d} (hy : y ∉ closedBall x a) :
    zeta a x y = 0 := by
  apply kern_eq_zero_of_lt_norm ha
  rw [mem_closedBall, dist_eq_norm, not_le] at hy
  rwa [← norm_neg, neg_sub]

theorem zeta_tsupport_subset {a : ℝ} (ha : 0 < a) (x : Vec d) :
    tsupport (zeta a x) ⊆ closedBall x a := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra h
  exact hy (zeta_eq_zero ha h)

theorem zeta_hasCompactSupport {a : ℝ} (ha : 0 < a) (x : Vec d) :
    HasCompactSupport (zeta a x) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x a) fun y hy => by
    by_contra h; exact hy (zeta_eq_zero ha h)

theorem fderiv_zeta (a : ℝ) (x y e : Vec d) :
    fderiv ℝ (zeta a x) y e = -fderiv ℝ (kern a) (x - y) e := by
  have h1 : HasFDerivAt (kern (d := d) a) (fderiv ℝ (kern a) (x - y)) (x - y) :=
    (((kern_smooth (d := d) a).differentiable (by simp)) (x - y)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vec d => x - y) (-(ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hasFDerivAt_id y).const_sub x
  have h3 : fderiv ℝ (zeta a x) y =
      fderiv ℝ (kern a) (x - y) ∘L (-(ContinuousLinearMap.id ℝ (Vec d))) := (h1.comp y h2).fderiv
  rw [h3]
  simp

theorem fderiv_kern_eq_zero_of_lt_norm {a : ℝ} (ha : 0 < a) {z : Vec d} (hz : a < ‖z‖) :
    fderiv ℝ (kern a) z = 0 := by
  have : kern (d := d) a =ᶠ[nhds z] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {w : Vec d | a < ‖w‖} := isOpen_lt continuous_const continuous_norm
    exact Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => kern_eq_zero_of_lt_norm ha hw
  rw [this.fderiv_eq]
  simp

end PDE.Parabolic.Energy
