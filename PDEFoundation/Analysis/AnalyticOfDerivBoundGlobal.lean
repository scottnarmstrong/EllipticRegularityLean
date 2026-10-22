module

public import PDEFoundation.Analysis.AnalyticOfDerivBoundSeries
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Analyticity from derivative bounds for globally smooth functions
-/

@[expose] public section

namespace PDE

open scoped Nat Topology

/-- A globally smooth function with locally uniform coordinate derivative
bounds has its factorial-scaled derivative series on every sufficiently short
supremum-norm ball. -/
theorem hasFPowerSeriesOnBall_of_global_coordinate_deriv_bound {d : ℕ}
    (g : Vec d → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x₀ : Vec d) {δ M K : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hcoord : ∀ y ∈ euclideanBall x₀ δ,
      ∀ n : ℕ, ∀ ι : Fin n → Fin d,
        |iteratedFDeriv ℝ n g y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * n) ^ n)
    (r : NNReal) (hr : 0 < r)
    (hrBall : (d : ℝ) * (r : ℝ) < δ)
    (hrGeom : (Real.exp 1 * K * d) * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall g (derivativePowerSeries g x₀) x₀ (r : ENNReal) := by
  let p := derivativePowerSeries g x₀
  have hx₀ : x₀ ∈ euclideanBall x₀ δ := by
    change euclideanSqDist x₀ x₀ < δ ^ 2
    rw [euclideanSqDist_self]
    positivity
  have hrad : (r : ENNReal) ≤ p.radius :=
    le_radius_factorial_iteratedFDeriv_of_coordinate_bound g x₀ hM hK
      (hcoord x₀ hx₀) r hrGeom.le
  refine ⟨hrad, ENNReal.coe_pos.mpr hr, ?_⟩
  intro h hh
  have hhNorm : ‖h‖ < (r : ℝ) := by
    simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using hh
  have hsum : (∑ i : Fin d, |h i|) < δ := by
    calc
      (∑ i : Fin d, |h i|) ≤ (d : ℝ) * ‖h‖ :=
        sum_abs_coordinates_le_card_mul_norm h
      _ ≤ (d : ℝ) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hhNorm.le (Nat.cast_nonneg d)
      _ < δ := hrBall
  have hsumNonneg : 0 ≤ ∑ i : Fin d, |h i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  let q : ℝ := Real.exp 1 * K * (∑ i : Fin d, |h i|)
  have hqNonneg : 0 ≤ q := by dsimp [q]; positivity
  have hqLt : q < 1 := by
    calc
      q ≤ (Real.exp 1 * K * d) * (r : ℝ) := by
        dsimp [q]
        have hsumLe : (∑ i : Fin d, |h i|) ≤ (d : ℝ) * (r : ℝ) :=
          (sum_abs_coordinates_le_card_mul_norm h).trans
            (mul_le_mul_of_nonneg_left hhNorm.le (Nat.cast_nonneg d))
        calc
          Real.exp 1 * K * (∑ i : Fin d, |h i|) ≤
              Real.exp 1 * K * ((d : ℝ) * (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hsumLe (mul_nonneg (Real.exp_pos 1).le hK)
          _ = (Real.exp 1 * K * d) * (r : ℝ) := by ring
      _ < 1 := hrGeom
  have hhRadius : h ∈ Metric.eball (0 : Vec d) p.radius := by
    rw [Metric.mem_eball] at hh ⊢
    exact lt_of_lt_of_le hh hrad
  have hpSum := p.hasSum hhRadius
  have hpow : Filter.Tendsto (fun n : ℕ => M * q ^ (n + 1)) Filter.atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLt).comp
      (Filter.tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, mul_zero] using h.const_mul M
  have hdiff : Filter.Tendsto
      (fun n : ℕ => g (x₀ + h) - ∑ k ∈ Finset.range (n + 1), p k (fun _ => h))
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hpow
    simpa only [Real.norm_eq_abs, p, derivativePowerSeries,
      smul_apply, smul_eq_mul, q] using
      abs_taylor_remainder_affine_line_le_geometric g hg x₀ h hδ hM hK hsum hcoord n
  have hpartial : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), p k (fun _ => h))
      Filter.atTop (𝓝 (g (x₀ + h))) := by
    have h := (tendsto_const_nhds (x := g (x₀ + h))).sub hdiff
    convert h using 1 <;> simp
  exact (hpSum.summable.hasSum_iff_tendsto_nat).2
    ((Filter.tendsto_add_atTop_iff_nat 1).1 hpartial)

/-- Globally smooth functions satisfying coordinate Cauchy-type bounds on a
round neighborhood are analytic at its center. -/
theorem analyticAt_of_global_coordinate_deriv_bound {d : ℕ}
    (g : Vec d → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x₀ : Vec d) {δ M K : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hcoord : ∀ y ∈ euclideanBall x₀ δ,
      ∀ n : ℕ, ∀ ι : Fin n → Fin d,
        |iteratedFDeriv ℝ n g y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * n) ^ n) :
    AnalyticAt ℝ g x₀ := by
  let A : ℝ := (d : ℝ)
  let B : ℝ := Real.exp 1 * K * d
  have hA : 0 ≤ A := Nat.cast_nonneg d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdenA : 0 < A + 1 := by linarith
  have hdenB : 0 < B + 1 := by linarith
  have hmin : 0 < min (δ / (A + 1)) (1 / (B + 1)) := by
    apply lt_min
    · exact div_pos hδ hdenA
    · exact div_pos zero_lt_one hdenB
  obtain ⟨ρ, hρpos, hρlt⟩ := exists_between hmin
  let r : NNReal := ⟨ρ, hρpos.le⟩
  have hr : 0 < r := hρpos
  have hrBall : (d : ℝ) * (r : ℝ) < δ := by
    have hρA : ρ < δ / (A + 1) := hρlt.trans_le (min_le_left _ _)
    have hmul : (A + 1) * ρ < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hdenA).mp hρA
    have hle : A * ρ ≤ (A + 1) * ρ :=
      mul_le_mul_of_nonneg_right (by linarith) hρpos.le
    exact hle.trans_lt hmul
  have hrGeom : (Real.exp 1 * K * d) * (r : ℝ) < 1 := by
    have hρB : ρ < 1 / (B + 1) := hρlt.trans_le (min_le_right _ _)
    have hmul : (B + 1) * ρ < 1 := by
      simpa only [mul_comm] using (lt_div_iff₀ hdenB).mp hρB
    have hle : B * ρ ≤ (B + 1) * ρ :=
      mul_le_mul_of_nonneg_right (by linarith) hρpos.le
    exact hle.trans_lt hmul
  exact (hasFPowerSeriesOnBall_of_global_coordinate_deriv_bound
    g hg x₀ hδ hM hK hcoord r hr hrBall hrGeom).analyticAt

end PDE
