module

public import PDEFoundation.Sobolev.Trace.Extension.FlatBasic

/-!
# The `L^p` bound for the flat pull-back

`∫ |ζ g ∘ Ψ₀|^p dx' ≤ C ∫ |g|^p dσ`, with `C = (sup |ζ|)^p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The `p`-th power of `g` along the boundary parametrisation, cut off to the chart ball. -/
noncomputable def flatPg (φ : GraphChart Ω) (p : ℝ) (g : Vec (n + 1) → ℝ) (x' : Vec n) :
    ℝ≥0∞ :=
  (euclideanBall φ.c φ.r).indicator
    (fun x' => ENNReal.ofReal (|g (φ.map (x', 0))| ^ p)) x'

theorem measurable_flatPg (φ : GraphChart Ω) (p : ℝ) {g : Vec (n + 1) → ℝ} (hg : Measurable g) :
    Measurable (flatPg φ p g) := by
  unfold flatPg
  refine Measurable.indicator ?_ φ.measurableSet_ball
  exact ENNReal.measurable_ofReal.comp
    ((continuous_abs.measurable.comp (hg.comp φ.measurable_boundaryMap)).pow_const p)

theorem lintegral_flatPg_le (φ : GraphChart Ω) (p : ℝ) {g : Vec (n + 1) → ℝ}
    (hg : AEMeasurable g (boundarySurfaceMeasure Ω)) :
    ∫⁻ x', flatPg φ p g x' ≤ ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω := by
  unfold flatPg
  rw [lintegral_indicator φ.measurableSet_ball]
  exact φ.lintegral_boundaryMap_le (f := fun x => ENNReal.ofReal (|g x| ^ p))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hg).pow_const p))

theorem ofReal_abs_flatPullback_rpow_le (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζU : tsupport ζ ⊆ φ.dom) {M p : ℝ} (hp : 0 < p) (hM : ∀ X, |ζ X| ≤ M)
    (g : Vec (n + 1) → ℝ) (x' : Vec n) :
    ENNReal.ofReal (|flatPullback φ ζ g x'| ^ p) ≤ ENNReal.ofReal (M ^ p) * flatPg φ p g x' := by
  by_cases hx : x' ∈ euclideanBall φ.c φ.r
  · simp only [flatPg, indicator_of_mem hx]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ((abs_nonneg _).trans (hM 0)) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.mul_rpow ((abs_nonneg _).trans (hM 0)) (abs_nonneg _)]
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hp.le
    rw [flatPullback, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  · rw [φ.flatPullback_eq_zero_of_notMem hζU g hx]
    simp [Real.zero_rpow hp.ne']

/-- **`L^p` bound for the flat pull-back.** -/
theorem flatPullback_Lp_le (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ} (hζc : Continuous ζ)
    (hζK : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ φ.dom) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, AEMeasurable g (boundarySurfaceMeasure Ω) →
      ∫⁻ x', ENNReal.ofReal (|flatPullback φ ζ g x'| ^ p) ≤
        C * ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂boundarySurfaceMeasure Ω := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_hasCompactSupport hζc hζK
  refine ⟨Real.toNNReal (M ^ p), fun g hg => ?_⟩
  calc ∫⁻ x', ENNReal.ofReal (|flatPullback φ ζ g x'| ^ p)
      ≤ ∫⁻ x', ENNReal.ofReal (M ^ p) * flatPg φ p g x' :=
        lintegral_mono (fun x' => ofReal_abs_flatPullback_rpow_le φ hζU (by linarith) hM g x')
    _ = ENNReal.ofReal (M ^ p) * ∫⁻ x', flatPg φ p g x' :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (lintegral_flatPg_le φ p hg)

end PDE.TraceLane
