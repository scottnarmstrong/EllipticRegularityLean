module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.LimitPointwise

/-!
# Friedland--Hayman: the cutoff limit

As `ε → 0+` the angular integrals of the cut-off lifts converge, by dominated convergence, to explicit
combinations of the Beta-type integrals `sinCos N q = ∫_0^{π/2} sin^{N-1} cos^q`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem measurable_cutoff (ε : ℝ) : Measurable (cutoff ε) := by
  unfold cutoff
  exact (Real.smoothTransition.continuous.comp
    ((continuous_id.sub continuous_const).div_const ε)).measurable

theorem measurable_radProf (ε a : ℝ) : Measurable (radProf ε a) := by
  unfold radProf
  exact (measurable_cutoff ε).mul (measurable_id.pow_const a)

theorem measurable_radProfD (ε a : ℝ) : Measurable (radProfD ε a) := by
  unfold radProfD cutoffD
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  have h1 : Continuous fun r : ℝ => deriv Real.smoothTransition ((r - ε) / ε) :=
    hd.comp ((continuous_id.sub continuous_const).div_const ε)
  exact ((measurable_const.mul h1.measurable).mul (measurable_id.pow_const a)).add
    ((measurable_cutoff ε).mul (measurable_const.mul (measurable_id.pow_const (a - 1))))

theorem measurable_numInt (n N : ℕ) (a I J ε : ℝ) : Measurable (numInt n N a I J ε) := by
  unfold numInt
  have h1 := (measurable_radProf ε a).comp Real.measurable_cos
  have h2 := (measurable_radProfD ε a).comp Real.measurable_cos
  fun_prop

theorem measurable_denInt (n N : ℕ) (a I ε : ℝ) : Measurable (denInt n N a I ε) := by
  unfold denInt
  have h1 := (measurable_radProf ε a).comp Real.measurable_cos
  fun_prop

theorem ae_ne_pi_div_two : ∀ᵐ θ : ℝ ∂volume, θ ≠ Real.pi / 2 := by
  have := (Set.countable_singleton (Real.pi / 2)).ae_notMem (volume : Measure ℝ)
  filter_upwards [this] with θ hθ
  simpa using hθ

theorem mem_Ioo_of_mem_uIoc {θ : ℝ} (h : θ ∈ Set.uIoc (0 : ℝ) (Real.pi / 2)) (h2 : θ ≠ Real.pi / 2) :
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at h
  exact ⟨h.1, lt_of_le_of_ne h.2 h2⟩

theorem tendsto_integral_numInt {n N : ℕ} (hn : 1 ≤ n) {a I J : ℝ} (ha : 0 ≤ a)
    (hp : -1 < (n : ℝ) + 2 * a - 3) (hI : 0 ≤ I) (hJ : 0 ≤ J) :
    Tendsto (fun ε => ∫ θ in (0 : ℝ)..(Real.pi / 2), numInt n N a I J ε θ) (𝓝[>] 0)
      (𝓝 (∫ θ in (0 : ℝ)..(Real.pi / 2), numLim n N a I J θ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_smoothTransition
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => sinCosInt N ((n : ℝ) + 2 * a - 3) θ * ((2 * K + a) ^ 2 * I + J + I)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε => (measurable_numInt n N a I J ε).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_ne_pi_div_two] with θ hθ hmem
    rw [Real.norm_eq_abs]
    exact numInt_le hn hε ha hI hJ hK hK0 (mem_Ioo_of_mem_uIoc hmem hθ)
  · exact (intervalIntegrable_sin_pow_mul_cos_rpow (N - 1) hp).mul_const _
  · filter_upwards [ae_ne_pi_div_two] with θ hθ hmem
    have hθ' := mem_Ioo_of_mem_uIoc hmem hθ
    exact tendsto_numInt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩)

theorem tendsto_integral_denInt {n N : ℕ} (hn : 1 ≤ n) {a I J : ℝ}
    (hp : -1 < (n : ℝ) + 2 * a - 3) (hI : 0 ≤ I) (hJ : 0 ≤ J) :
    Tendsto (fun ε => ∫ θ in (0 : ℝ)..(Real.pi / 2), denInt n N a I ε θ) (𝓝[>] 0)
      (𝓝 (∫ θ in (0 : ℝ)..(Real.pi / 2), denLim n N a I θ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_smoothTransition
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => sinCosInt N ((n : ℝ) + 2 * a - 3) θ * ((2 * K + a) ^ 2 * I + J + I)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε => (measurable_denInt n N a I ε).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_ne_pi_div_two] with θ hθ hmem
    rw [Real.norm_eq_abs]
    exact denInt_le hn hI hJ (mem_Ioo_of_mem_uIoc hmem hθ)
  · exact (intervalIntegrable_sin_pow_mul_cos_rpow (N - 1) hp).mul_const _
  · filter_upwards [ae_ne_pi_div_two] with θ hθ hmem
    have hθ' := mem_Ioo_of_mem_uIoc hmem hθ
    exact tendsto_denInt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩)

theorem sinCos_eq_integral (N : ℕ) (q : ℝ) :
    sinCos N q = ∫ θ in (0 : ℝ)..(Real.pi / 2), sinCosInt N q θ := rfl

theorem integral_numLim {n N : ℕ} (hn : 1 ≤ n) {a I J : ℝ}
    (hp : -1 < (n : ℝ) + 2 * a - 3) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), numLim n N a I J θ =
      a ^ 2 * I * (sinCos N ((n : ℝ) + 2 * a - 3) - sinCos N ((n : ℝ) + 2 * a - 3 + 2)) +
        J * sinCos N ((n : ℝ) + 2 * a - 3) := by
  have hp2 : -1 < (n : ℝ) + 2 * a - 3 + 2 := by linarith
  have h1 : IntervalIntegrable (sinCosInt N ((n : ℝ) + 2 * a - 3)) volume 0 (Real.pi / 2) :=
    intervalIntegrable_sin_pow_mul_cos_rpow (N - 1) hp
  have h2 : IntervalIntegrable (sinCosInt N ((n : ℝ) + 2 * a - 3 + 2)) volume 0 (Real.pi / 2) :=
    intervalIntegrable_sin_pow_mul_cos_rpow (N - 1) hp2
  have : ∫ θ in (0 : ℝ)..(Real.pi / 2), numLim n N a I J θ =
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (a ^ 2 * I * (sinCosInt N ((n : ℝ) + 2 * a - 3) θ - sinCosInt N ((n : ℝ) + 2 * a - 3 + 2) θ) +
          J * sinCosInt N ((n : ℝ) + 2 * a - 3) θ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    exact numLim_eq hn (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [this, intervalIntegral.integral_add ((h1.sub h2).const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub h1 h2]
  rfl

theorem integral_denLim {n N : ℕ} (hn : 1 ≤ n) {a I : ℝ} :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), denLim n N a I θ =
      I * sinCos N ((n : ℝ) + 2 * a - 3 + 2) := by
  have : ∫ θ in (0 : ℝ)..(Real.pi / 2), denLim n N a I θ =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), I * sinCosInt N ((n : ℝ) + 2 * a - 3 + 2) θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    exact denLim_eq hn (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [this, intervalIntegral.integral_const_mul]
  rfl

end Susp

end

end PDE.FHLane
