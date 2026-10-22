module

public import PDEFoundation.Sobolev.Trace.Model.TracePolar
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The radial kernel of the flat pull-back estimate

`flatRadKer n p a b s = (min a (b s))^p / s^(n+p-1)` is the radial kernel that controls the
off-diagonal contribution of a cut-off in the flat Gagliardo seminorm.  For `p > 1` it is
integrable over `Vec n` (polar coordinates reduce this to `∫ r^{-p}` at infinity), and its
integral is translation invariant in either variable.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

/-- The radial kernel `s ↦ min(a, b s)^p / s^(n+p-1)`, as an extended nonnegative real. -/
noncomputable def flatRadKer (n : ℕ) (p a b s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min a (b * s) ^ p / s ^ ((n : ℝ) + p - 1))

theorem measurable_flatRadKer (n : ℕ) (p a b : ℝ) : Measurable (flatRadKer n p a b) :=
  ENNReal.measurable_ofReal.comp
    (((measurable_const.min (measurable_const.mul measurable_id)).pow_const p).div
      (measurable_id.pow_const _))

theorem measurable_flatRadKer_norm (n m : ℕ) (p a b : ℝ) :
    Measurable (fun z : Vec m => flatRadKer n p a b (vecEuclideanNorm z)) :=
  (measurable_flatRadKer n p a b).comp measurable_vecEuclideanNorm

/-- Radial identity: `r^(n-1) · m^p / r^(n+p-1) = m^p / r^p`. -/
theorem pow_mul_div_rpow_eq {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (m p : ℝ) :
    r ^ (n - 1) * (m / r ^ ((n : ℝ) + p - 1)) = m / r ^ p := by
  have h : ((n : ℝ) + p - 1) = ((n - 1 : ℕ) : ℝ) + p := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [h, Real.rpow_add hr, Real.rpow_natCast]
  have : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
  have : r ^ p ≠ 0 := (Real.rpow_pos_of_pos hr p).ne'
  field_simp

theorem lintegral_Ioi_rpow_neg_lt_top {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : 0 < t) :
    ∫⁻ r in Ioi t, ENNReal.ofReal (r ^ (-p)) < ∞ :=
  (integrableOn_Ioi_rpow_of_lt (by linarith) ht).lintegral_lt_top

/-- Finiteness of the radial kernel integral. -/
theorem lintegral_flatRadKer_lt_top (n : ℕ) [NeZero n] {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) < ∞ := by
  obtain ⟨c, hctop, hc⟩ := exists_lintegral_comp_vecEuclideanNorm n
  rw [hc _ (measurable_flatRadKer n p a b)]
  refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hctop) ?_
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hp0 : 0 < p := by linarith
  set f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (n - 1)) * flatRadKer n p a b r with hf
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine lt_of_le_of_lt (lintegral_union_le _ _ _) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · calc ∫⁻ r in Ioc (0 : ℝ) 1, f r ≤ ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (b ^ p) := by
          refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
          simp only [hf, flatRadKer]
          rw [← ENNReal.ofReal_mul (pow_nonneg hr.1.le _), pow_mul_div_rpow_eq hn hr.1]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hr.1 p), ← Real.mul_rpow hb hr.1.le]
          exact Real.rpow_le_rpow (le_min ha (mul_nonneg hb hr.1.le)) (min_le_right _ _) hp0.le
      _ < ∞ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
  · calc ∫⁻ r in Ioi (1 : ℝ), f r ≤ ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (a ^ p) *
          ENNReal.ofReal (r ^ (-p)) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun r hr => ?_)
          have hr0 : 0 < r := zero_lt_one.trans hr
          simp only [hf, flatRadKer]
          rw [← ENNReal.ofReal_mul (pow_nonneg hr0.le _), pow_mul_div_rpow_eq hn hr0,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv]
          refine div_le_div_of_nonneg_right ?_ (Real.rpow_pos_of_pos hr0 p).le
          exact Real.rpow_le_rpow (le_min ha (mul_nonneg hb hr0.le)) (min_le_left _ _) hp0.le
      _ < ∞ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ioi_rpow_neg_lt_top hp one_pos)

/-- Translation invariance of the kernel integral in the second variable. -/
theorem lintegral_flatRadKer_sub_left (n : ℕ) (p a b : ℝ) (x : Vec n) :
    ∫⁻ y : Vec n, flatRadKer n p a b (vecEuclideanNorm (x - y)) =
      ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) :=
  lintegral_sub_left_eq_self (fun z : Vec n => flatRadKer n p a b (vecEuclideanNorm z)) x

/-- Translation invariance of the kernel integral in the first variable. -/
theorem lintegral_flatRadKer_sub_right (n : ℕ) (p a b : ℝ) (y : Vec n) :
    ∫⁻ x : Vec n, flatRadKer n p a b (vecEuclideanNorm (x - y)) =
      ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) :=
  lintegral_sub_right_eq_self (fun z : Vec n => flatRadKer n p a b (vecEuclideanNorm z)) y

theorem measurable_flatRadKer_sub (n : ℕ) (p a b : ℝ) :
    Measurable (fun q : Vec n × Vec n => flatRadKer n p a b (vecEuclideanNorm (q.1 - q.2))) :=
  measurable_flatRadKer_norm n n p a b |>.comp (measurable_fst.sub measurable_snd)

theorem measurable_flatRadKer_sub_left (n : ℕ) (p a b : ℝ) (x : Vec n) :
    Measurable (fun y : Vec n => flatRadKer n p a b (vecEuclideanNorm (x - y))) :=
  (measurable_flatRadKer_norm n n p a b).comp (measurable_const.sub measurable_id)

theorem measurable_flatRadKer_sub_right (n : ℕ) (p a b : ℝ) (y : Vec n) :
    Measurable (fun x : Vec n => flatRadKer n p a b (vecEuclideanNorm (x - y))) :=
  (measurable_flatRadKer_norm n n p a b).comp (measurable_id.sub measurable_const)

/-- Convolution bound, density in the first variable. -/
theorem lintegral_lintegral_mul_flatRadKer_left (n : ℕ) (p a b : ℝ) {P : Vec n → ℝ≥0∞}
    (hP : Measurable P) :
    ∫⁻ x : Vec n, ∫⁻ y : Vec n, P x * flatRadKer n p a b (vecEuclideanNorm (x - y)) =
      (∫⁻ x, P x) * ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) := by
  have h : ∀ x : Vec n, ∫⁻ y : Vec n, P x * flatRadKer n p a b (vecEuclideanNorm (x - y)) =
      P x * ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) := fun x => by
    rw [lintegral_const_mul _ (measurable_flatRadKer_sub_left n p a b x),
      lintegral_flatRadKer_sub_left]
  simp_rw [h]
  exact lintegral_mul_const'' _ hP.aemeasurable

/-- Convolution bound, density in the second variable. -/
theorem lintegral_lintegral_mul_flatRadKer_right (n : ℕ) (p a b : ℝ) {P : Vec n → ℝ≥0∞}
    (hP : Measurable P) :
    ∫⁻ x : Vec n, ∫⁻ y : Vec n, P y * flatRadKer n p a b (vecEuclideanNorm (x - y)) =
      (∫⁻ x, P x) * ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) := by
  have hm : Measurable (fun q : Vec n × Vec n =>
      P q.2 * flatRadKer n p a b (vecEuclideanNorm (q.1 - q.2))) :=
    (hP.comp measurable_snd).mul (measurable_flatRadKer_sub n p a b)
  rw [lintegral_lintegral_swap (f := fun x y => P y * flatRadKer n p a b
    (vecEuclideanNorm (x - y))) hm.aemeasurable]
  have h : ∀ y : Vec n, ∫⁻ x : Vec n, P y * flatRadKer n p a b (vecEuclideanNorm (x - y)) =
      P y * ∫⁻ z : Vec n, flatRadKer n p a b (vecEuclideanNorm z) := fun y => by
    rw [lintegral_const_mul _ (measurable_flatRadKer_sub_right n p a b y),
      lintegral_flatRadKer_sub_right]
  simp_rw [h]
  exact lintegral_mul_const'' _ hP.aemeasurable

end PDE.TraceLane
