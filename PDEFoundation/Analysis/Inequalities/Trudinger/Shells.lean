module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Dyadic shell estimates for the Riesz kernel (Trudinger, Steps 2 and 3)

The near part of the Riesz potential is bounded by the maximal function, and the
far kernel `|z|^{-d}` has logarithmic integral, both by dyadic ball decompositions.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

theorem mem_euclideanBall_iff_norm_sub_lt (x y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    y ∈ euclideanBall x ρ ↔ vecEuclideanNorm (x - y) < ρ := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ, vecEuclideanNorm_sub_comm]

theorem measurable_norm_sub (x : Vec d) : Measurable fun y => vecEuclideanNorm (x - y) :=
  (continuous_vecEuclideanNorm.comp (continuous_const.sub continuous_id)).measurable

/-- A positive `r < ε` lies in a dyadic scale `(1/2)^(k+1) ε ≤ r < (1/2)^k ε`. -/
theorem exists_dyadic_scale {r ε : ℝ} (hr : 0 < r) (hrε : r < ε) :
    ∃ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) * ε ≤ r ∧ r < (1 / 2 : ℝ) ^ k * ε := by
  classical
  have hε : 0 < ε := hr.trans hrε
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * ε ≤ r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hε) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hε] at hn
    calc (1 / 2 : ℝ) ^ (n + 1) * ε ≤ (1 / 2) ^ n * ε := by
          rw [pow_succ]
          have : 0 < (1 / 2 : ℝ) ^ n * ε := by positivity
          nlinarith
      _ ≤ r := hn.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · simpa using hrε
  · have := Nat.find_min hex (m := k) (by omega)
    simpa [pow_succ] using not_le.mp this

theorem near_term_eq {a : ℝ} (ha : 0 < a) :
    (a / 2) ^ ((1 : ℝ) - d) * a ^ d = 2 ^ d / 2 * a := by
  rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_natCast, div_pow]
  field_simp

/-- Near part of the Riesz potential (Trudinger, Step 2): if all ball averages of `f` around `x`
are at most `m`, then `∫_{B_ε(x)} |x - y|^{1-d} f ≤ 2^d |B₁| ε m`. -/
theorem lintegral_near_le (hd : 2 ≤ d) (x : Vec d) {ε m : ℝ} (hε : 0 < ε) (hm : 0 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (havg : ∀ ρ : ℝ, 0 < ρ →
      ∫⁻ y in euclideanBall x ρ, f y ≤ ENNReal.ofReal m * volume (euclideanBall x ρ)) :
    ∫⁻ y in euclideanBall x ε,
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y ≤
      ENNReal.ofReal (2 ^ d * ε * m) * volume (euclideanBall (0 : Vec d) 1) := by
  set ρ : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * ε with hρdef
  have hρ : ∀ k, 0 < ρ k := fun k => by positivity
  have hρs : ∀ k, ρ (k + 1) = ρ k / 2 := fun k => by simp only [hρdef, pow_succ]; ring
  have hpt : ∀ y ∈ euclideanBall x ε,
      ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y ≤
        ∑' k, (euclideanBall x (ρ k)).indicator
          (fun y => ENNReal.ofReal (ρ (k + 1) ^ ((1 : ℝ) - d)) * f y) y := by
    intro y hy
    have hr := (mem_euclideanBall_iff_norm_sub_lt x y hε).1 hy
    rcases (vecEuclideanNorm_nonneg (x - y)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)]
      simp
    · obtain ⟨k, hk1, hk2⟩ := exists_dyadic_scale hpos hr
      refine le_trans ?_ (ENNReal.le_tsum k)
      rw [Set.indicator_of_mem ((mem_euclideanBall_iff_norm_sub_lt x y (hρ k)).2 hk2)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact Real.rpow_le_rpow_of_nonpos (hρ (k + 1)) hk1 (by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
  have hmeas : ∀ k, Measurable ((euclideanBall x (ρ k)).indicator
      (fun y => ENNReal.ofReal (ρ (k + 1) ^ ((1 : ℝ) - d)) * f y)) := fun k =>
    (hf.const_mul _).indicator (measurableSet_euclideanBall _ _)
  calc ∫⁻ y in euclideanBall x ε,
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y
      ≤ ∫⁻ y in euclideanBall x ε, ∑' k, (euclideanBall x (ρ k)).indicator
          (fun y => ENNReal.ofReal (ρ (k + 1) ^ ((1 : ℝ) - d)) * f y) y :=
        setLIntegral_mono' (measurableSet_euclideanBall _ _) hpt
    _ ≤ ∫⁻ y, ∑' k, (euclideanBall x (ρ k)).indicator
          (fun y => ENNReal.ofReal (ρ (k + 1) ^ ((1 : ℝ) - d)) * f y) y :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k, ∫⁻ y, (euclideanBall x (ρ k)).indicator
          (fun y => ENNReal.ofReal (ρ (k + 1) ^ ((1 : ℝ) - d)) * f y) y :=
        lintegral_tsum fun k => (hmeas k).aemeasurable
    _ ≤ ∑' k : ℕ, (ENNReal.ofReal (2 ^ d / 2 * ε * m) * 2⁻¹ ^ k) *
          volume (euclideanBall (0 : Vec d) 1) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [lintegral_indicator (measurableSet_euclideanBall _ _), lintegral_const_mul _ hf]
        refine (mul_le_mul' le_rfl (havg _ (hρ k))).trans ?_
        rw [volume_euclideanBall_eq_unit_mul_of_pos x (hρ k), ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine le_of_eq (congrArg (· * _) ?_)
        have hreal : ρ (k + 1) ^ ((1 : ℝ) - d) * m * ρ k ^ d =
            2 ^ d / 2 * ε * m * (1 / 2 : ℝ) ^ k := by
          rw [hρs k, mul_right_comm, near_term_eq (hρ k)]
          simp only [hρdef]; ring
        rw [hreal, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num [ENNReal.ofReal_div_of_pos]
    _ = ENNReal.ofReal (2 ^ d * ε * m) * volume (euclideanBall (0 : Vec d) 1) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        congr 1
        have : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [this, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
