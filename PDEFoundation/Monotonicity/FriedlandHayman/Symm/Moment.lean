module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Polarization

/-!
# Friedland--Hayman: polarization increases the height moment

For a continuous `g` on the sphere and `e` with `⟪u, e⟫ ≥ 0`, polarization toward `u` increases
`∫ g x ⟪x, e⟫`, strictly if some point of the open half-sphere `⟪x, u⟫ > 0` has `g x < g (ρ x)`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane

noncomputable section

variable {D : ℕ}

namespace Symm

variable (u : HilbertVec D) (hu : ‖u‖ = 1)

theorem inner_rho_right (x : Sph D) (e : HilbertVec D) :
    inner ℝ (rho u hu x : HilbertVec D) e =
      inner ℝ (x : HilbertVec D) e - 2 * (inner ℝ (x : HilbertVec D) u * inner ℝ u e) := by
  rw [coe_rho, inner_sub_left, inner_smul_left]
  simp only [conj_trivial]
  ring

/-- The integrand of the gain of the height moment. -/
def momentGain (g : C(Sph D, ℝ)) (e : HilbertVec D) (x : Sph D) : ℝ :=
  (max (g x) (g (rho u hu x)) - g x) *
    (2 * (inner ℝ (x : HilbertVec D) u * inner ℝ u e))

theorem continuous_momentGain (g : C(Sph D, ℝ)) (e : HilbertVec D) :
    Continuous (momentGain u hu g e) := by
  unfold momentGain
  exact ((g.continuous.max (g.continuous.comp (continuous_rho u hu))).sub g.continuous).mul
    (continuous_const.mul ((continuous_subtype_val.inner continuous_const).mul continuous_const))

theorem moment_gain_eq (g : C(Sph D, ℝ)) (e : HilbertVec D) :
    ∫ x, polarize u hu g x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D) -
      ∫ x, g x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D) =
    ∫ x, (halfPos u).indicator (momentGain u hu g e) x ∂(sphMeasure D) := by
  have hc : ∀ F : C(Sph D, ℝ), Integrable (fun x => F x * inner ℝ (x : HilbertVec D) e)
      (sphMeasure D) := fun F =>
    integrable_of_continuous (F.continuous.mul (continuous_subtype_val.inner continuous_const))
  rw [← integral_sub (hc _) (hc _)]
  have hW : Integrable (fun x => polarize u hu g x * inner ℝ (x : HilbertVec D) e -
      g x * inner ℝ (x : HilbertVec D) e) (sphMeasure D) := (hc _).sub (hc _)
  rw [integral_split u hu hW]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases h : x ∈ halfPos u
  · have h' : 0 < inner ℝ (x : HilbertVec D) u := h
    simp only [indicator_of_mem h, momentGain, polarize_of_pos u hu g h',
      polarize_rho_of_pos u hu g h', inner_rho_right]
    rcases le_total (g x) (g (rho u hu x)) with hab | hab
    · rw [max_eq_right hab, min_eq_left hab]; ring
    · rw [max_eq_left hab, min_eq_right hab]; ring
  · simp [indicator_of_notMem h]

theorem momentGain_nonneg (g : C(Sph D, ℝ)) {e : HilbertVec D} (he : 0 ≤ inner ℝ u e) {x : Sph D}
    (hx : x ∈ halfPos u) : 0 ≤ momentGain u hu g e x := by
  have h' : 0 < inner ℝ (x : HilbertVec D) u := hx
  exact mul_nonneg (sub_nonneg.2 (le_max_left _ _)) (by positivity)

end Symm

open Symm

variable (u : HilbertVec D) (hu : ‖u‖ = 1)

/-- Polarization toward `e` increases the height moment (weakly). -/
theorem integral_polarize_mul_inner_ge (g : C(Sph D, ℝ)) {e : HilbertVec D}
    (he : 0 ≤ inner ℝ u e) :
    ∫ x, g x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D) ≤
      ∫ x, polarize u hu g x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D) := by
  rw [← sub_nonneg, moment_gain_eq]
  refine integral_nonneg fun x => ?_
  by_cases h : x ∈ halfPos u
  · rw [indicator_of_mem h]; exact momentGain_nonneg u hu g he h
  · rw [indicator_of_notMem h]; exact le_rfl

/-- Strict increase of the height moment when mass is moved. -/
theorem integral_polarize_mul_inner_gt (g : C(Sph D, ℝ)) {e : HilbertVec D}
    (he : 0 < inner ℝ u e) {x₀ : Sph D} (hx₀ : 0 < inner ℝ (x₀ : HilbertVec D) u)
    (hlt : g x₀ < g (sphMap (reflection' u hu) x₀)) :
    ∫ x, g x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D) <
      ∫ x, polarize u hu g x * inner ℝ (x : HilbertVec D) e ∂(sphMeasure D) := by
  rw [← sub_pos, moment_gain_eq]
  have hI : Integrable ((halfPos u).indicator (momentGain u hu g e)) (sphMeasure D) :=
    (integrable_of_continuous (continuous_momentGain u hu g e)).indicator (measurableSet_halfPos u)
  have hnn : 0 ≤ (halfPos u).indicator (momentGain u hu g e) := fun x => by
    by_cases h : x ∈ halfPos u
    · rw [indicator_of_mem h]; exact momentGain_nonneg u hu g he.le h
    · rw [indicator_of_notMem h]; exact le_rfl
  rw [integral_pos_iff_support_of_nonneg hnn hI]
  set U : Set (Sph D) := halfPos u ∩ {x | g x < g (rho u hu x)} with hU
  have hUo : IsOpen U := (isOpen_halfPos u).inter
    (isOpen_lt g.continuous (g.continuous.comp (continuous_rho u hu)))
  have hUne : U.Nonempty := ⟨x₀, hx₀, hlt⟩
  refine lt_of_lt_of_le (hUo.measure_pos _ hUne) (measure_mono ?_)
  rintro x ⟨hxA, hxlt⟩
  have h' : 0 < inner ℝ (x : HilbertVec D) u := hxA
  rw [Function.mem_support, indicator_of_mem hxA]
  have : 0 < momentGain u hu g e x := by
    unfold momentGain
    have : g x < max (g x) (g (rho u hu x)) := lt_max_of_lt_right hxlt
    exact mul_pos (sub_pos.2 this) (by positivity)
  exact this.ne'

end

end PDE.FHLane
