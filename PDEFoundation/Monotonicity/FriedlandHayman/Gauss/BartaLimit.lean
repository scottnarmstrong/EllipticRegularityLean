module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.BartaLocal

/-!
# Friedland--Hayman: the boundary term of Barta's inequality vanishes

We prove the Cauchy--Schwarz type bound `g(a)² ≤ (a - τ) ∫_τ^a g'²` for `g(τ) = 0`, the vanishing
of `∫_{(τ, a]} f` as `a ↓ τ` for integrable `f`, and conclude that
`F a = (φ'/φ) g² w → 0` as `a ↓ τ`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

theorem sq_le_mul_integral_sq {τ a : ℝ} {g g' : ℝ → ℝ} (hτa : τ < a)
    (hg : ContinuousOn g (Icc τ a)) (hg0 : g τ = 0)
    (hder : ∀ x ∈ Ioo τ a, HasDerivAt g (g' x) x) (h1 : IntervalIntegrable g' volume τ a)
    (h2 : IntervalIntegrable (fun x => g' x ^ 2) volume τ a) :
    g a ^ 2 ≤ (a - τ) * ∫ x in τ..a, g' x ^ 2 := by
  have hI1 : ∫ x in τ..a, g' x = g a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτa.le hg hder h1, hg0, sub_zero]
  set k : ℝ := g a / (a - τ) with hk
  have hpos : 0 < a - τ := sub_pos.mpr hτa
  have hexp : ∫ x in τ..a, (g' x - k) ^ 2
      = (∫ x in τ..a, g' x ^ 2) - 2 * k * (∫ x in τ..a, g' x) + k ^ 2 * (a - τ) := by
    have e : (fun x => (g' x - k) ^ 2) = fun x => (g' x ^ 2 - 2 * k * g' x) + k ^ 2 := by
      funext x; ring
    rw [e, intervalIntegral.integral_add (h2.sub (h1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub h2 (h1.const_mul _), intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hnn : 0 ≤ ∫ x in τ..a, (g' x - k) ^ 2 :=
    intervalIntegral.integral_nonneg hτa.le (fun x _ => sq_nonneg _)
  rw [hexp, hI1] at hnn
  have hk2 : k * (a - τ) = g a := by rw [hk]; field_simp
  have : k ^ 2 * (a - τ) = g a ^ 2 / (a - τ) := by rw [hk]; field_simp
  have h3 : 2 * k * g a = 2 * g a ^ 2 / (a - τ) := by rw [hk]; field_simp
  rw [this, h3] at hnn
  have h4 : g a ^ 2 / (a - τ) ≤ ∫ x in τ..a, g' x ^ 2 := by
    have : 2 * g a ^ 2 / (a - τ) = 2 * (g a ^ 2 / (a - τ)) := by ring
    linarith
  rw [div_le_iff₀ hpos] at h4
  linarith

theorem tendsto_setIntegral_Ioc_zero {τ : ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi τ)) :
    Tendsto (fun a => ∫ x in Ioc τ a, f x) (𝓝[>] τ) (𝓝 0) := by
  have e : ∀ a, ∫ x in Ioc τ a, f x = ∫ x in Ioi τ, (Iic a).indicator f x := by
    intro a
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.Iic_inter_Ioi]
  simp_rw [e]
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi τ))
    (l := 𝓝[>] τ) (F := fun a x => (Iic a).indicator f x) (f := fun _ => (0 : ℝ))
    (fun x => ‖f x‖) (Eventually.of_forall fun a => hf.aestronglyMeasurable.indicator measurableSet_Iic)
    (Eventually.of_forall fun a => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _)
    hf.norm ?_
  · simpa using this
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show τ < x from hx)] with a ha
    rw [indicator_of_notMem]
    exact fun h => absurd (mem_Iic.mp h) (not_le.mpr ha.2)

end

end PDE.FHLane
