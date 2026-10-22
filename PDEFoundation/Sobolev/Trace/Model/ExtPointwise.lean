module

public import PDEFoundation.Sobolev.Trace.Model.ExtFormula
public import PDEFoundation.Sobolev.Trace.Model.ExtJensen
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Pointwise bounds for the extension and its convolution kernels

For `t > 0` we bound `|(ρ_t * g)(x)|^p` by the Jensen average `∫ K(x - y, t) |g y|^p dy` and the
convolutions with the derivative profiles by the oscillation of `g` on the Euclidean ball
`B(x, t)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {n : ℕ}

/-- The closed Euclidean ball `{y | |x - y| ≤ t}`. -/
def eBallSet (n : ℕ) (x : Vec n) (t : ℝ) : Set (Vec n) := {y | vecEuclideanNorm (x - y) ≤ t}

theorem continuous_vecEuclideanNorm (n : ℕ) : Continuous (vecEuclideanNorm : Vec n → ℝ) := by
  unfold vecEuclideanNorm vecNormSq vecDot
  fun_prop

theorem measurableSet_eBallSet (x : Vec n) (t : ℝ) : MeasurableSet (eBallSet n x t) :=
  measurableSet_le ((continuous_vecEuclideanNorm n).comp
    (continuous_const.sub continuous_id)).measurable measurable_const

theorem eBallSet_subset_closedBall (x : Vec n) (t : ℝ) :
    eBallSet n x t ⊆ Metric.closedBall x t := by
  intro y hy
  have h : ‖x - y‖ ≤ t := (norm_le_vecEuclideanNorm _).trans hy
  rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
  exact h

theorem volume_eBallSet_le (x : Vec n) {t : ℝ} (ht : 0 ≤ t) :
    volume (eBallSet n x t) ≤ ENNReal.ofReal ((2 * t) ^ n) := by
  refine (measure_mono (eBallSet_subset_closedBall x t)).trans ?_
  rw [Real.volume_pi_closedBall x ht]
  simp

theorem dil_kernel_nonneg {t : ℝ} (ht : 0 < t) (z : Vec n) : 0 ≤ dil n (extKernel n) z t :=
  mul_nonneg (pow_nonneg (inv_nonneg.2 ht.le) _) (extKernel_nonneg n _)

theorem lintegral_ofReal_dil_sub {t : ℝ} (ht : 0 < t) (x : Vec n) :
    ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) t) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_dil n (isProfile_extKernel n) ht x)
    (Filter.Eventually.of_forall fun y => dil_kernel_nonneg ht _),
    integral_dil_sub n ht, extKernel_integral]
  rw [mul_one, ← mul_pow] 
  simp [inv_mul_cancel₀ ht.ne']

theorem ofReal_abs_dilConv_rpow_le {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ} (hgm : Measurable g)
    {t : ℝ} (ht : 0 < t) (x : Vec n) :
    ENNReal.ofReal (|dilConv n (extKernel n) g (x, t)| ^ p) ≤
      ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) t) * ENNReal.ofReal (|g y| ^ p) := by
  have h1 : ENNReal.ofReal |dilConv n (extKernel n) g (x, t)| ≤
      ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) t) * ENNReal.ofReal |g y| := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (dil_kernel_nonneg ht _),
      ENNReal.ofReal_mul (dil_kernel_nonneg ht _)]
  have hw : Measurable fun y => ENNReal.ofReal (dil n (extKernel n) (x - y) t) :=
    ENNReal.measurable_ofReal.comp (continuous_dil_sub n (isProfile_extKernel n) t x).measurable
  have hf : Measurable fun y => ENNReal.ofReal |g y| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hgm)
  have h2 := lintegral_mul_rpow_le volume hp hw.aemeasurable hf.aemeasurable
  rw [lintegral_ofReal_dil_sub ht x, ENNReal.one_rpow, one_mul] at h2
  have hp0 : 0 ≤ p := by linarith
  calc ENNReal.ofReal (|dilConv n (extKernel n) g (x, t)| ^ p)
      = ENNReal.ofReal |dilConv n (extKernel n) g (x, t)| ^ p :=
        (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0).symm
    _ ≤ _ := ENNReal.rpow_le_rpow h1 hp0
    _ ≤ _ := h2
    _ = _ := by
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0]

theorem ofReal_abs_dilConv_le_ball {k : ℕ} {ψ : Vec n → ℝ} (hψ : IsProfile ψ)
    (h0 : ∫ z, ψ z = 0) {M : ℝ} (hM : ∀ w, |ψ w| ≤ M) {g : Vec n → ℝ}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : Vec n) :
    ENNReal.ofReal |dilConv k ψ g (x, t)| ≤ ENNReal.ofReal (M * (t⁻¹) ^ k) *
      ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y := by
  rw [dilConv_eq_sub k hψ h0 hg ht x, ← Real.enorm_eq_ofReal_abs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
  by_cases hy : y ∈ eBallSet n x t
  · rw [indicator_of_mem hy, Real.enorm_eq_ofReal_abs, abs_mul,
      ENNReal.ofReal_mul (abs_nonneg _)]
    refine mul_le_mul_left ?_ _
    exact ENNReal.ofReal_le_ofReal ((abs_dil_le k hM ht _).trans (le_of_eq (mul_comm _ _)))
  · rw [indicator_of_notMem hy]
    have : dil k ψ (x - y) t = 0 := dil_eq_zero k hψ ht (lt_of_not_ge hy)
    simp [this]

theorem ball_integral_rpow_le {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ} (hgm : Measurable g)
    {t : ℝ} (ht : 0 < t) (x : Vec n) :
    (∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y) ^ p ≤
      ENNReal.ofReal ((2 * t) ^ n) ^ (p - 1) *
        ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y := by
  have hp0 : 0 ≤ p := by linarith
  have hf : Measurable fun y => ENNReal.ofReal |g y - g x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hgm.sub_const _))
  have hw : Measurable ((eBallSet n x t).indicator (1 : Vec n → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_eBallSet x t)
  have h := lintegral_mul_rpow_le volume hp hw.aemeasurable hf.aemeasurable
  have e1 : ∀ y, (eBallSet n x t).indicator (1 : Vec n → ℝ≥0∞) y * ENNReal.ofReal |g y - g x| =
      (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y := by
    intro y
    by_cases hy : y ∈ eBallSet n x t <;> simp [hy]
  have e2 : ∀ y, (eBallSet n x t).indicator (1 : Vec n → ℝ≥0∞) y *
      ENNReal.ofReal |g y - g x| ^ p =
      (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y := by
    intro y
    by_cases hy : y ∈ eBallSet n x t
    · simp [hy, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0]
    · simp [hy]
  simp_rw [e1, e2] at h
  rw [lintegral_indicator_one (measurableSet_eBallSet x t)] at h
  refine h.trans ?_
  refine mul_le_mul_left ?_ _
  exact ENNReal.rpow_le_rpow (volume_eBallSet_le x ht.le) (by linarith)

theorem real_scalar_alg (n : ℕ) {p M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t) :
    (M * (t⁻¹) ^ (n + 1)) ^ p * ((2 * t) ^ n) ^ (p - 1) =
      M ^ p * (2 : ℝ) ^ ((n : ℝ) * (p - 1)) * t ^ (-((n : ℝ) + p)) := by
  have ha : ((t⁻¹) ^ (n + 1)) ^ p = t ^ (-(((n : ℝ) + 1) * p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 ht.le), Real.inv_rpow ht.le,
      ← Real.rpow_neg ht.le]
    push_cast
    ring_nf
  have hb : ((2 * t) ^ n) ^ (p - 1) = (2 : ℝ) ^ ((n : ℝ) * (p - 1)) * t ^ ((n : ℝ) * (p - 1)) := by
    rw [← Real.rpow_natCast (2 * t) n, ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) ht.le]
  rw [Real.mul_rpow hM (by positivity), ha, hb]
  have : t ^ (-((n : ℝ) + p)) = t ^ (-(((n : ℝ) + 1) * p)) * t ^ ((n : ℝ) * (p - 1)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [this]
  ring

theorem rball_rpow_le {p : ℝ} (hp : 1 < p) {M : ℝ} (hM0 : 0 ≤ M) {g : Vec n → ℝ}
    (hgm : Measurable g) {t : ℝ} (ht : 0 < t) (x : Vec n) :
    (ENNReal.ofReal (M * (t⁻¹) ^ (n + 1)) *
        ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y) ^ p ≤
      ENNReal.ofReal (M ^ p * (2 : ℝ) ^ ((n : ℝ) * (p - 1)) * t ^ (-((n : ℝ) + p))) *
        ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y := by
  have hp0 : 0 ≤ p := by linarith
  have hc : 0 ≤ M * (t⁻¹) ^ (n + 1) := mul_nonneg hM0 (pow_nonneg (inv_nonneg.2 ht.le) _)
  have h2 := ball_integral_rpow_le hp hgm ht x
  have hb : 0 ≤ ((2 * t) ^ n) := pow_nonneg (by positivity) _
  calc (ENNReal.ofReal (M * (t⁻¹) ^ (n + 1)) *
          ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y) ^ p
      = ENNReal.ofReal (M * (t⁻¹) ^ (n + 1)) ^ p *
          (∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal |g y - g x|) y) ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ hp0
    _ ≤ ENNReal.ofReal (M * (t⁻¹) ^ (n + 1)) ^ p * (ENNReal.ofReal ((2 * t) ^ n) ^ (p - 1) *
        ∫⁻ y, (eBallSet n x t).indicator (fun y => ENNReal.ofReal (|g y - g x| ^ p)) y) :=
        mul_le_mul_right h2 _
    _ = _ := by
        rw [← mul_assoc, ENNReal.ofReal_rpow_of_nonneg hc hp0,
          ENNReal.ofReal_rpow_of_nonneg hb (by linarith), ← ENNReal.ofReal_mul
            (Real.rpow_nonneg hc _), real_scalar_alg n hM0 ht]

end PDE.TraceLane
