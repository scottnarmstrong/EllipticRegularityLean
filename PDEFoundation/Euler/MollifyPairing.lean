module

public import PDEFoundation.Euler.MollifyLocal

/-!
# Pairing identity for periodic mollification

For `f`, `ψ` periodic with `f` locally integrable and `ψ` continuous,
`∫_cube (molK a ⋆ f) ψ = ∫ t, molK a t * ∫_cube f(x) ψ(t + x) dx`.
Consequently mollification commutes with tests against smooth periodic functions.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE

/-- The box `[-(a+1), a+2]²` containing `cube - {‖t‖ ≤ a}`. -/
def mollBox (a : ℝ) : Set (Vec 2) := Icc (fun _ => -(a + 1)) (fun _ => a + 2)

theorem measurableSet_torusCube : MeasurableSet torusCube := measurableSet_Icc

theorem mollify_pairing {a : ℝ} (ha : 0 < a) {f ψ : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hloc : LocallyIntegrable f volume) (hψ : Continuous ψ) (hψp : IsTorusPeriodic ψ) :
    Integrable (fun t => molK a t * ∫ x in torusCube, f x * ψ (t + x)) ∧
    ∫ x in torusCube, mollify a f x * ψ x =
      ∫ t, molK a t * ∫ x in torusCube, f x * ψ (t + x) := by
  set S := mollBox a with hS
  set fS : Vec 2 → ℝ := S.indicator f with hfS
  set Ψ : Vec 2 → ℝ := torusCube.indicator ψ with hΨ
  have hfSint : Integrable fS :=
    (hloc.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hΨm : Measurable Ψ := hψ.measurable.indicator measurableSet_torusCube
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hψ.continuousOn
  have hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C := by
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ torusCube
    · rw [hΨ, Set.indicator_of_mem hx]; exact (hC x hx).trans (le_max_left _ _)
    · rw [hΨ, Set.indicator_of_notMem hx]; simp
  have hG : Integrable (fun p : Vec 2 × Vec 2 => molK a p.2 * fS (p.1 - p.2)) (volume.prod volume) :=
    (molK_integrable ha).convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hfSint
  have hF : Integrable (fun p : Vec 2 × Vec 2 => Ψ p.1 * (molK a p.2 * fS (p.1 - p.2)))
      (volume.prod volume) :=
    hG.bdd_mul (hΨm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (Classical.choose_spec hΨb) p.1)
  have hpt : ∀ x t : Vec 2, Ψ x * (molK a t * fS (x - t)) = Ψ x * (molK a t * f (x - t)) := by
    intro x t
    by_cases hx : x ∈ torusCube
    · by_cases ht : a < ‖t‖
      · rw [molK_eq_zero ha ht]; simp
      · have hmem : x - t ∈ S := by
          have hti : ∀ i, |t i| ≤ a := fun i => (norm_le_pi_norm t i).trans (not_lt.mp ht)
          have hx0 : ∀ i, 0 ≤ x i := fun i => hx.1 i
          have hx1 : ∀ i, x i ≤ 1 := fun i => hx.2 i
          constructor <;> intro i <;> simp only [Pi.sub_apply] <;>
            linarith [hx0 i, hx1 i, abs_le.mp (hti i)]
        rw [hfS, Set.indicator_of_mem hmem]
    · rw [hΨ, Set.indicator_of_notMem hx]; simp
  have hlhs : ∫ x in torusCube, mollify a f x * ψ x =
      ∫ x, ∫ t, Ψ x * (molK a t * fS (x - t)) := by
    rw [← integral_indicator measurableSet_torusCube]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpt, integral_const_mul]
    by_cases hx : x ∈ torusCube
    · simp [Set.indicator_of_mem hx, hΨ, mollify_apply, mul_comm]
    · simp [Set.indicator_of_notMem hx, hΨ]
  have hinner : ∀ t, ∫ x, Ψ x * (molK a t * fS (x - t)) =
      molK a t * ∫ x in torusCube, f x * ψ (t + x) := by
    intro t
    simp only [hpt]
    have hgp : IsTorusPeriodic (fun y => f y * ψ (t + y)) := by
      intro i y
      simp only
      rw [hf i y, show t + (y + basisVec i) = (t + y) + basisVec i by abel, hψp i]
    have htr := hgp.setIntegral_cube_add (-t)
    rw [← htr, ← integral_indicator measurableSet_torusCube, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ torusCube
    · simp only [hΨ, Set.indicator_of_mem hx, sub_eq_add_neg]
      rw [show t + (x + -t) = x by abel]
      ring
    · simp [hΨ, Set.indicator_of_notMem hx]
  have hint : Integrable (fun t => ∫ x, Ψ x * (molK a t * fS (x - t))) :=
    hF.integral_prod_right
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hint
  · rw [hlhs, integral_integral_swap hF]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)

theorem integral_cube_mollify_mul {a : ℝ} (ha : 0 < a) {f ψ : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hloc : LocallyIntegrable f volume) (hψ : Continuous ψ) (hψp : IsTorusPeriodic ψ) :
    ∫ x in torusCube, mollify a f x * ψ x =
      ∫ t, molK a t * ∫ x in torusCube, f x * ψ (t + x) :=
  (mollify_pairing ha hf hloc hψ hψp).2

theorem integrable_mollify_pairing {a : ℝ} (ha : 0 < a) {f ψ : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hloc : LocallyIntegrable f volume) (hψ : Continuous ψ) (hψp : IsTorusPeriodic ψ) :
    Integrable (fun t => molK a t * ∫ x in torusCube, f x * ψ (t + x)) :=
  (mollify_pairing ha hf hloc hψ hψp).1

end PDE
