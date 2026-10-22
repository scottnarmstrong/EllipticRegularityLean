module

public import PDEFoundation.Euler.MollifyPairing

/-!
# Symmetry of periodic mollification

For `ℤ²`-periodic locally integrable `f`, `g`, a.e. bounded, `∫_cube (molK ⋆ g) f = ∫_cube (molK ⋆ f) g`
(the mollifier is even).  This is the pairing identity of `MollifyPairing` for bounded measurable (instead
of continuous) test functions, followed by a translation.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE

theorem molK_neg (a : ℝ) (y : Vec 2) : molK a (-y) = molK a y := by
  unfold molK scaledConvexApproxKernel unitConvexApproxKernel
  simp only [smul_neg]
  rw [ContDiffBump.normed_neg]

/-- Pairing identity for a bounded measurable periodic test function. -/
theorem mollify_pairing_bdd {a : ℝ} (ha : 0 < a) {f ψ : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hloc : LocallyIntegrable f volume) (hψm : AEStronglyMeasurable ψ volume) {C : ℝ}
    (hψB : ∀ᵐ x ∂(volume : Measure (Vec 2)), |ψ x| ≤ C) (hψp : IsTorusPeriodic ψ) :
    ∫ x in torusCube, mollify a f x * ψ x =
      ∫ t, molK a t * ∫ x in torusCube, f x * ψ (t + x) := by
  set S := mollBox a with hS
  set fS : Vec 2 → ℝ := S.indicator f with hfS
  set Ψ : Vec 2 → ℝ := torusCube.indicator ψ with hΨ
  have hfSint : Integrable fS :=
    (hloc.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hΨm : AEStronglyMeasurable Ψ volume := hψm.indicator measurableSet_torusCube
  have hΨB : ∀ᵐ x ∂(volume : Measure (Vec 2)), ‖Ψ x‖ ≤ C := by
    filter_upwards [hψB] with x hx
    by_cases hxc : x ∈ torusCube
    · rw [hΨ, Set.indicator_of_mem hxc, Real.norm_eq_abs]; exact hx
    · rw [hΨ, Set.indicator_of_notMem hxc, norm_zero]
      exact (abs_nonneg _).trans hx
  have hG : Integrable (fun p : Vec 2 × Vec 2 => molK a p.2 * fS (p.1 - p.2)) (volume.prod volume) :=
    (molK_integrable ha).convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hfSint
  have hF : Integrable (fun p : Vec 2 × Vec 2 => Ψ p.1 * (molK a p.2 * fS (p.1 - p.2)))
      (volume.prod volume) :=
    hG.bdd_mul hΨm.comp_fst
      ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Vec 2)))
        (ν := (volume : Measure (Vec 2)))).ae hΨB)
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
  rw [hlhs, integral_integral_swap hF]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- **Symmetry of mollification on the torus.** -/
theorem integral_cube_mollify_mul_comm {a : ℝ} (ha : 0 < a) {f g : Vec 2 → ℝ}
    (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g)
    (hfl : LocallyIntegrable f volume) (hgl : LocallyIntegrable g volume) {Bf Bg : ℝ}
    (hfB : ∀ᵐ x ∂(volume : Measure (Vec 2)), |f x| ≤ Bf)
    (hgB : ∀ᵐ x ∂(volume : Measure (Vec 2)), |g x| ≤ Bg) :
    ∫ x in torusCube, mollify a g x * f x = ∫ x in torusCube, mollify a f x * g x := by
  rw [mollify_pairing_bdd ha hg hgl hfl.aestronglyMeasurable hfB hf,
    mollify_pairing_bdd ha hf hfl hgl.aestronglyMeasurable hgB hg]
  rw [← integral_neg_eq_self (fun t => molK a t * ∫ x in torusCube, f x * g (t + x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [molK_neg]
  congr 1
  have hp : IsTorusPeriodic (fun y => f y * g (-t + y)) := by
    intro i y
    simp only
    rw [hf i y, show -t + (y + basisVec i) = (-t + y) + basisVec i by abel, hg i]
  have htr := hp.setIntegral_cube_add t
  rw [← htr]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show -t + (x + t) = x by abel, mul_comm, add_comm t x]

end PDE
