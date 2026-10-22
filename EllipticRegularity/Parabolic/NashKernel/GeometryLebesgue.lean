module

public import EllipticRegularity.Parabolic.NashKernel.Geometry
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Product cubes and Lebesgue differentiation on `Vec d × Vec d`

Here `Metric.closedBall` is used on purpose: on `Vec d` and `Vec d × Vec d` it is a cube for the
supremum metric, and cubes are the sets used in the Lebesgue differentiation theorem
(`IsUnifLocDoublingMeasure.ae_tendsto_average`).  Round balls are `euclideanBall`.

* the product cube `closedBall (x, y) δ = closedBall x δ ×ˢ closedBall y δ` and its volume,
* a ready-to-use Lebesgue differentiation corollary and a two-sided-bound corollary,
* limit passage as `δ → 0⁺` for the Gaussian lower/upper expressions.
-/

@[expose] public section

namespace PDE.NashKernelGeometry

open MeasureTheory Metric Filter Topology Set

/-- The product measure space structure on `Vec d × Vec d` is `volume.prod volume`. -/
theorem volume_prod_eq (d : ℕ) :
    (volume : Measure (Vec d × Vec d)) = (volume : Measure (Vec d)).prod volume := rfl

/-- The sup-cube about `(x, y)` is the product of the sup-cubes (Mathlib `closedBall_prod_same`). -/
theorem closedBall_prod {d : ℕ} (x y : Vec d) (δ : ℝ) :
    closedBall (x, y) δ = closedBall x δ ×ˢ closedBall y δ :=
  (closedBall_prod_same x y δ).symm

/-- Volume of a sup-cube in `Vec d`. -/
theorem volume_closedBall_vec {d : ℕ} (x : Vec d) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (closedBall x δ) = ENNReal.ofReal ((2 * δ) ^ d) := by
  simpa using Real.volume_pi_closedBall x hδ

/-- Volume of a product sup-cube is the product of the volumes. -/
theorem volume_closedBall_prod {d : ℕ} (x y : Vec d) (δ : ℝ) :
    volume (closedBall (x, y) δ) = volume (closedBall x δ) * volume (closedBall y δ) := by
  rw [closedBall_prod, volume_prod_eq, Measure.prod_prod]

/-- Explicit volume of a product sup-cube. -/
theorem volume_closedBall_prod_eq {d : ℕ} (x y : Vec d) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (closedBall (x, y) δ) = ENNReal.ofReal ((2 * δ) ^ d) * ENNReal.ofReal ((2 * δ) ^ d) := by
  rw [volume_closedBall_prod, volume_closedBall_vec x hδ, volume_closedBall_vec y hδ]

section Differentiation

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [SecondCountableTopology α]
  [BorelSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]

/-- Lebesgue differentiation along any family of cubes shrinking to the center (fixed center). -/
theorem ae_tendsto_average_closedBall {F : α → ℝ} (hF : LocallyIntegrable F μ)
    {ι : Type*} {l : Filter ι} (δ : ι → ℝ) (hδ : Tendsto δ l (𝓝[>] 0)) :
    ∀ᵐ p ∂μ, Tendsto (fun j => ⨍ q in closedBall p (δ j), F q ∂μ) l (𝓝 (F p)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hF 1] with p hp
  have hpos := eventually_mem_of_tendsto_nhdsWithin hδ
  exact hp (fun _ => p) δ hδ (hpos.mono fun j hj => by
    rw [one_mul]; exact mem_closedBall_self (le_of_lt hj))

/-- Upper half of the two-sided corollary: if for a.e. `p` and all small `δ` the cube averages of
`F` are at most `U p + η δ` with `η δ → 0` as `δ → 0⁺`, then `F ≤ U` a.e. -/
theorem ae_le_of_average_le {F U : α → ℝ} (hF : LocallyIntegrable F μ) {η : ℝ → ℝ}
    (hη : Tendsto η (𝓝[>] 0) (𝓝 0))
    (h : ∀ᵐ p ∂μ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ⨍ q in closedBall p δ, F q ∂μ ≤ U p + η δ) :
    ∀ᵐ p ∂μ, F p ≤ U p := by
  filter_upwards [ae_tendsto_average_closedBall hF (id : ℝ → ℝ) tendsto_id, h] with p hp hp'
  have h2 : Tendsto (fun δ : ℝ => U p + η δ) (𝓝[>] 0) (𝓝 (U p + 0)) :=
    tendsto_const_nhds.add hη
  rw [add_zero] at h2
  exact le_of_tendsto_of_tendsto hp h2 hp'

/-- Lower half of the two-sided corollary. -/
theorem ae_ge_of_average_ge {F L : α → ℝ} (hF : LocallyIntegrable F μ) {η : ℝ → ℝ}
    (hη : Tendsto η (𝓝[>] 0) (𝓝 0))
    (h : ∀ᵐ p ∂μ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), L p - η δ ≤ ⨍ q in closedBall p δ, F q ∂μ) :
    ∀ᵐ p ∂μ, L p ≤ F p := by
  filter_upwards [ae_tendsto_average_closedBall hF (id : ℝ → ℝ) tendsto_id, h] with p hp hp'
  have h2 : Tendsto (fun δ : ℝ => L p - η δ) (𝓝[>] 0) (𝓝 (L p - 0)) :=
    tendsto_const_nhds.sub hη
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto h2 hp hp'

/-- Two-sided bound: if for a.e. `p` and all small `δ` the cube averages of `F` lie in
`[L p - η δ, U p + η δ]` with `η → 0` as `δ → 0⁺`, then `L ≤ F ≤ U` a.e. -/
theorem ae_bounds_of_average_bounds {F L U : α → ℝ} (hF : LocallyIntegrable F μ) {η : ℝ → ℝ}
    (hη : Tendsto η (𝓝[>] 0) (𝓝 0))
    (h : ∀ᵐ p ∂μ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      L p - η δ ≤ ⨍ q in closedBall p δ, F q ∂μ ∧ ⨍ q in closedBall p δ, F q ∂μ ≤ U p + η δ) :
    ∀ᵐ p ∂μ, L p ≤ F p ∧ F p ≤ U p := by
  have h1 := ae_ge_of_average_ge hF hη (h.mono fun p hp => hp.mono fun δ hδ => hδ.1)
  have h2 := ae_le_of_average_le hF hη (h.mono fun p hp => hp.mono fun δ hδ => hδ.2)
  filter_upwards [h1, h2] with p a b using ⟨a, b⟩

end Differentiation

/-- Lebesgue differentiation on `Vec d × Vec d` with sup-cubes `closedBall p δ`. -/
theorem ae_tendsto_average_closedBall_prod {d : ℕ} {F : Vec d × Vec d → ℝ}
    (hF : LocallyIntegrable F volume) {ι : Type*} {l : Filter ι} (δ : ι → ℝ)
    (hδ : Tendsto δ l (𝓝[>] 0)) :
    ∀ᵐ p : Vec d × Vec d, Tendsto (fun j => ⨍ q in closedBall p (δ j), F q) l (𝓝 (F p)) :=
  ae_tendsto_average_closedBall hF δ hδ

/-- Two-sided bound on `Vec d × Vec d` (statement of `ae_bounds_of_average_bounds` there). -/
theorem ae_bounds_of_average_bounds_prod {d : ℕ} {F L U : Vec d × Vec d → ℝ}
    (hF : LocallyIntegrable F volume) {η : ℝ → ℝ} (hη : Tendsto η (𝓝[>] 0) (𝓝 0))
    (h : ∀ᵐ p : Vec d × Vec d, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      L p - η δ ≤ ⨍ q in closedBall p δ, F q ∧ ⨍ q in closedBall p δ, F q ≤ U p + η δ) :
    ∀ᵐ p : Vec d × Vec d, L p ≤ F p ∧ F p ≤ U p :=
  ae_bounds_of_average_bounds hF hη h

section Limits

/-- The shrunk radius `max 0 (ρ - 2√d δ)` tends to `ρ` (`ρ ≥ 0`) as `δ → 0⁺`. -/
theorem tendsto_shrunk_radius (d : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (fun δ : ℝ => max 0 (ρ - 2 * Real.sqrt d * δ)) (𝓝[>] 0) (𝓝 ρ) := by
  have h : Tendsto (fun δ : ℝ => ρ - 2 * Real.sqrt d * δ) (𝓝 0) (𝓝 (ρ - 2 * Real.sqrt d * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_id)
  rw [mul_zero, sub_zero] at h
  have h2 : Tendsto (fun δ : ℝ => max 0 (ρ - 2 * Real.sqrt d * δ)) (𝓝 0) (𝓝 (max 0 ρ)) :=
    tendsto_const_nhds.max h
  rw [show max 0 ρ = ρ from max_eq_right hρ] at h2
  exact h2.mono_left nhdsWithin_le_nhds

/-- The enlarged radius `ρ + 2√d δ` tends to `ρ` as `δ → 0⁺`. -/
theorem tendsto_enlarged_radius (d : ℕ) (ρ : ℝ) :
    Tendsto (fun δ : ℝ => ρ + 2 * Real.sqrt d * δ) (𝓝[>] 0) (𝓝 ρ) := by
  have h : Tendsto (fun δ : ℝ => ρ + 2 * Real.sqrt d * δ) (𝓝 0) (𝓝 (ρ + 2 * Real.sqrt d * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
  rw [mul_zero, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Limit of the pure Gaussian upper expression along the shrunk radius:
`C h^{-d/2} exp(-r(δ)²/(8Λh)) → C h^{-d/2} exp(-ρ²/(8Λh))` for `r(δ) = max 0 (ρ - 2√d δ)`. -/
theorem tendsto_upper_gaussian (d : ℕ) (C Lam h : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (fun δ : ℝ => C * h ^ (-(d : ℝ) / 2) *
        Real.exp (-(max 0 (ρ - 2 * Real.sqrt d * δ)) ^ 2 / (8 * Lam * h))) (𝓝[>] 0)
      (𝓝 (C * h ^ (-(d : ℝ) / 2) * Real.exp (-ρ ^ 2 / (8 * Lam * h)))) := by
  have hr := tendsto_shrunk_radius d hρ
  have hc : Continuous fun r : ℝ => C * h ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (8 * Lam * h)) := by
    fun_prop
  exact (hc.tendsto ρ).comp hr

/-- Limit of the unabsorbed upper expression (the `nashAronsonUpper` bound with `√((d+2)/2)`). -/
theorem tendsto_upper_expression (d : ℕ) (C Lam h : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (fun δ : ℝ => C * h ^ (-(d : ℝ) / 2) *
        Real.exp (-(max 0 (ρ - 2 * Real.sqrt d * δ)) ^ 2 / (4 * Lam * h) +
          Real.sqrt (((d : ℝ) + 2) / 2) * (max 0 (ρ - 2 * Real.sqrt d * δ)) /
            Real.sqrt (Lam * h))) (𝓝[>] 0)
      (𝓝 (C * h ^ (-(d : ℝ) / 2) *
        Real.exp (-ρ ^ 2 / (4 * Lam * h) + Real.sqrt (((d : ℝ) + 2) / 2) * ρ /
          Real.sqrt (Lam * h)))) := by
  have hr := tendsto_shrunk_radius d hρ
  have hc : Continuous fun r : ℝ => C * h ^ (-(d : ℝ) / 2) *
      Real.exp (-r ^ 2 / (4 * Lam * h) + Real.sqrt (((d : ℝ) + 2) / 2) * r /
        Real.sqrt (Lam * h)) := by
    fun_prop
  exact (hc.tendsto ρ).comp hr

/-- Limit of the lower Gaussian expression along the enlarged radius:
`c h^{-d/2} exp(-β (ρ + 2√d δ)²/h) → c h^{-d/2} exp(-β ρ²/h)`. -/
theorem tendsto_lower_gaussian (d : ℕ) (c β h ρ : ℝ) :
    Tendsto (fun δ : ℝ => c * h ^ (-(d : ℝ) / 2) *
        Real.exp (-β * (ρ + 2 * Real.sqrt d * δ) ^ 2 / h)) (𝓝[>] 0)
      (𝓝 (c * h ^ (-(d : ℝ) / 2) * Real.exp (-β * ρ ^ 2 / h))) := by
  have hr := tendsto_enlarged_radius d ρ
  have hc : Continuous fun r : ℝ => c * h ^ (-(d : ℝ) / 2) * Real.exp (-β * r ^ 2 / h) := by
    fun_prop
  exact (hc.tendsto ρ).comp hr

end Limits

end PDE.NashKernelGeometry

