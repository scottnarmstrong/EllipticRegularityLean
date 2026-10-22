module

public import PDEFoundation.Measure.AxisBoxVolume
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Shrinking collars in planar axis boxes

This module records the vanishing of the integral of an integrable density
over boundary collars whose width tends to zero.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace PDE

open Filter MeasureTheory Set

/-- An integrable function has vanishing integral on any measurable sets which
eventually exclude every point. This is the dominated-convergence core used by
shrinking-collar estimates. -/
theorem tendsto_setIntegral_of_integrable_of_eventually_not_mem
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {f : X → E} (hf : Integrable f μ) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n))
    (hvanish : ∀ x, ∀ᶠ n in atTop, x ∉ s n) :
    Tendsto (fun n => ∫ x in s n, f x ∂μ) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable ((s n).indicator f) μ := fun n =>
    hf.aestronglyMeasurable.indicator (hs n)
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖(s n).indicator f x‖ ≤ ‖f x‖ := fun n =>
    ae_of_all _ fun x => norm_indicator_le_norm_self _ _
  have hlimit : ∀ᵐ x ∂μ,
      Tendsto (fun n => (s n).indicator f x) atTop (𝓝 0) := by
    apply ae_of_all
    intro x
    apply Filter.EventuallyEq.tendsto
    exact (hvanish x).mono fun n hn => by
      simp only [indicator_of_notMem hn]
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    hmeas hf.norm hbound hlimit
  simpa only [integral_indicator (hs _), integral_zero] using h

/-- The width-`δ` part of an open planar axis cube left outside its closed
`(r - δ)`-core. This is a literal boundary collar, with no metric-ball
interpretation involved. -/
def centeredAxisCubeBoundaryCollar (x₀ : Vec 2) (r δ : ℝ) : Set (Vec 2) :=
  centeredAxisCube x₀ r \ closedCenteredAxisCube x₀ (r - δ)

theorem measurableSet_centeredAxisCubeBoundaryCollar (x₀ : Vec 2) (r δ : ℝ) :
    MeasurableSet (centeredAxisCubeBoundaryCollar x₀ r δ) :=
  (isOpen_centeredAxisCube x₀ r).measurableSet.diff
    (isClosed_closedCenteredAxisCube x₀ (r - δ)).measurableSet

/-- The integral of an integrable density over a planar square boundary collar
tends to zero whenever its width tends to zero. The statement is deliberately
valid for signed/vector-valued densities; squared `L²` densities are the
immediate scalar application. -/
theorem tendsto_setIntegral_centeredAxisCubeBoundaryCollar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ : Vec 2) (r : ℝ) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    {f : Vec 2 → E} (hf : Integrable f volume) :
    Tendsto (fun n => ∫ x in centeredAxisCubeBoundaryCollar x₀ r (δ n), f x)
      atTop (𝓝 0) := by
  apply tendsto_setIntegral_of_integrable_of_eventually_not_mem hf
    (fun n => centeredAxisCubeBoundaryCollar x₀ r (δ n))
  · exact fun n => measurableSet_centeredAxisCubeBoundaryCollar x₀ r (δ n)
  intro x
  by_cases hx : x ∈ centeredAxisCube x₀ r
  · have hx0 : x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r := by
      simpa only [centeredAxisCube, axisBox, Set.mem_pi, Set.mem_univ,
        forall_true_left, Set.mem_Ioo] using hx 0 (Set.mem_univ 0)
    have hx1 : x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r := by
      simpa only [centeredAxisCube, axisBox, Set.mem_pi, Set.mem_univ,
        forall_true_left, Set.mem_Ioo] using hx 1 (Set.mem_univ 1)
    let ε : ℝ := min
      (min (x 0 - (x₀ 0 - r)) (x₀ 0 + r - x 0))
      (min (x 1 - (x₀ 1 - r)) (x₀ 1 + r - x 1))
    have hεpos : 0 < ε := by
      dsimp [ε]
      apply lt_min
      · apply lt_min <;> linarith [hx0.1, hx0.2]
      · apply lt_min <;> linarith [hx1.1, hx1.2]
    have hε0l : ε ≤ x 0 - (x₀ 0 - r) := by
      dsimp [ε]
      exact (min_le_left _ _).trans (min_le_left _ _)
    have hε0u : ε ≤ x₀ 0 + r - x 0 := by
      dsimp [ε]
      exact (min_le_left _ _).trans (min_le_right _ _)
    have hε1l : ε ≤ x 1 - (x₀ 1 - r) := by
      dsimp [ε]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hε1u : ε ≤ x₀ 1 + r - x 1 := by
      dsimp [ε]
      exact (min_le_right _ _).trans (min_le_right _ _)
    filter_upwards [hδ.eventually_lt_const hεpos] with n hn
    intro hcollar
    apply hcollar.2
    intro i _
    fin_cases i
    · change x₀ 0 - (r - δ n) ≤ x 0 ∧ x 0 ≤ x₀ 0 + (r - δ n)
      constructor <;> linarith [hn.le, hε0l, hε0u]
    · change x₀ 1 - (r - δ n) ≤ x 1 ∧ x 1 ≤ x₀ 1 + (r - δ n)
      constructor <;> linarith [hn.le, hε1l, hε1u]
  · exact Eventually.of_forall fun _ hcollar => hx hcollar.1

/-- Restricted-domain form of the shrinking-collar estimate. This is the
version for local Sobolev energies: it only asks integrability on the fixed
square containing every collar. -/
theorem tendsto_setIntegral_centeredAxisCubeBoundaryCollar_of_integrableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ : Vec 2) (r : ℝ) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    {f : Vec 2 → E} (hf : IntegrableOn f (centeredAxisCube x₀ r)) :
    Tendsto (fun n => ∫ x in centeredAxisCubeBoundaryCollar x₀ r (δ n), f x)
      atTop (𝓝 0) := by
  let Q : Set (Vec 2) := centeredAxisCube x₀ r
  have hQ : MeasurableSet Q := (isOpen_centeredAxisCube x₀ r).measurableSet
  have hindicator : Integrable (Q.indicator f) volume :=
    hf.integrable_indicator hQ
  have hlimit := tendsto_setIntegral_centeredAxisCubeBoundaryCollar x₀ r hδ
    hindicator
  refine hlimit.congr' ?_
  filter_upwards with n
  apply setIntegral_congr_fun
    (measurableSet_centeredAxisCubeBoundaryCollar x₀ r (δ n))
  intro x hx
  exact indicator_of_mem hx.1 _

/-- Square-density specialization of the local shrinking-collar estimate. In
particular it applies to each scalar component of an `L²` weak gradient once
the corresponding square has been made integrable on the ambient square. -/
theorem tendsto_setIntegral_sq_centeredAxisCubeBoundaryCollar
    (x₀ : Vec 2) (r : ℝ) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    {g : Vec 2 → ℝ}
    (hg : IntegrableOn (fun x => (g x) ^ 2) (centeredAxisCube x₀ r)) :
    Tendsto (fun n =>
      ∫ x in centeredAxisCubeBoundaryCollar x₀ r (δ n), (g x) ^ 2)
      atTop (𝓝 0) :=
  tendsto_setIntegral_centeredAxisCubeBoundaryCollar_of_integrableOn x₀ r hδ hg

/-- The canonical width sequence `r / (n + 2)` tends to zero. -/
theorem tendsto_canonicalAxisBoxCollarWidth (r : ℝ) :
    Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_add_atTop_iff_nat 2).2
      (tendsto_const_div_atTop_nhds_zero_nat r)

/-- The integral of an integrable density on the canonical square collar of
width `r / (n + 2)` tends to zero. -/
theorem tendsto_setIntegral_canonical_centeredAxisCubeBoundaryCollar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ : Vec 2) (r : ℝ) {f : Vec 2 → E} (hf : Integrable f volume) :
    Tendsto (fun n : ℕ =>
      ∫ x in centeredAxisCubeBoundaryCollar x₀ r (r / ((n : ℝ) + 2)), f x)
      atTop (𝓝 0) :=
  tendsto_setIntegral_centeredAxisCubeBoundaryCollar x₀ r
    (tendsto_canonicalAxisBoxCollarWidth r) hf

/-- The canonical-width square collar has vanishing local square energy. -/
theorem tendsto_setIntegral_sq_canonical_centeredAxisCubeBoundaryCollar
    (x₀ : Vec 2) (r : ℝ) {g : Vec 2 → ℝ}
    (hg : IntegrableOn (fun x => (g x) ^ 2) (centeredAxisCube x₀ r)) :
    Tendsto (fun n : ℕ =>
      ∫ x in centeredAxisCubeBoundaryCollar x₀ r (r / ((n : ℝ) + 2)),
        (g x) ^ 2) atTop (𝓝 0) :=
  tendsto_setIntegral_sq_centeredAxisCubeBoundaryCollar x₀ r
    (tendsto_canonicalAxisBoxCollarWidth r) hg

/-- Any family of sets contained in the canonical shrinking square collar
has vanishing integral for a nonnegative square density. -/
theorem tendsto_setIntegral_sq_of_subset_canonical_centeredAxisCubeBoundaryCollar
    (x₀ : Vec 2) (r : ℝ) {g : Vec 2 → ℝ}
    (hg : IntegrableOn (fun x => (g x) ^ 2) (centeredAxisCube x₀ r))
    (s : ℕ → Set (Vec 2))
    (hs : ∀ n, s n ⊆
      centeredAxisCubeBoundaryCollar x₀ r (r / ((n : ℝ) + 2))) :
    Tendsto (fun n : ℕ => ∫ x in s n, (g x) ^ 2) atTop (𝓝 0) := by
  have hfull :=
    tendsto_setIntegral_sq_canonical_centeredAxisCubeBoundaryCollar x₀ r hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hfull
  · intro n
    exact integral_nonneg fun _ => sq_nonneg _
  · intro n
    apply setIntegral_mono_set
      (hg.mono_set sdiff_subset)
      (Filter.Eventually.of_forall fun x => sq_nonneg (g x))
      (Filter.Eventually.of_forall fun x hx => hs n hx)

end PDE
