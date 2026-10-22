module

public import PDEFoundation.Euler.MollifySymm

/-!
# Symmetry of periodic mollification, `L¹` times bounded

`∫_cube (molK ⋆ g) f = ∫_cube (molK ⋆ f) g` for `ℤ²`-periodic `f` locally integrable and `g` locally integrable
and a.e. bounded (e.g. `f` an `L²` datum).
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE

theorem mollify_pairing_L1 {a : ℝ} (ha : 0 < a) {f g : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hfl : LocallyIntegrable f volume) (hg : IsTorusPeriodic g) (hgl : LocallyIntegrable g volume)
    {Bg : ℝ} (hgB : ∀ᵐ x ∂(volume : Measure (Vec 2)), |g x| ≤ Bg) :
    ∫ x in torusCube, mollify a g x * f x =
      ∫ t, molK a t * ∫ x in torusCube, g x * f (t + x) := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  have hfint : Integrable f μc := hfl.integrableOn_isCompact isCompact_Icc
  have hq : Measure.QuasiMeasurePreserving (fun p : Vec 2 × Vec 2 => p.1 - p.2)
      (μc.prod volume) volume :=
    (QuasiMeasurePreserving.snd (measurePreserving_prod_sub_swap (volume : Measure (Vec 2))
      (volume : Measure (Vec 2))).quasiMeasurePreserving).mono_left
      (Measure.AbsolutelyContinuous.prod (Measure.restrict_le_self.absolutelyContinuous)
        Measure.AbsolutelyContinuous.rfl)
  have hmeas : AEStronglyMeasurable (fun p : Vec 2 × Vec 2 => f p.1 * (molK a p.2 * g (p.1 - p.2)))
      (μc.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Vec 2 × Vec 2 => g (p.1 - p.2)) (μc.prod volume) := by
      exact hgl.aestronglyMeasurable.comp_quasiMeasurePreserving hq
    exact hfint.aestronglyMeasurable.comp_fst.mul
      (((molK_contDiff a).continuous.aestronglyMeasurable.comp_snd).mul h1)
  have hbound : ∀ᵐ p ∂(μc.prod (volume : Measure (Vec 2))),
      ‖f p.1 * (molK a p.2 * g (p.1 - p.2))‖ ≤ ‖f p.1‖ * (molK a p.2 * Bg) := by
    filter_upwards [hq.ae hgB] with p hp
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (molK_nonneg ha _)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (molK_nonneg ha _)) (abs_nonneg _)
  have hF : Integrable (fun p : Vec 2 × Vec 2 => f p.1 * (molK a p.2 * g (p.1 - p.2))) (μc.prod volume) :=
    Integrable.mono' ((hfint.norm).mul_prod ((molK_integrable ha).mul_const Bg)) hmeas hbound
  have hlhs : ∫ x in torusCube, mollify a g x * f x = ∫ x, ∫ t, f x * (molK a t * g (x - t)) ∂volume ∂μc := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mollify_apply]
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  rw [hlhs, integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have hp : IsTorusPeriodic (fun y => f y * g (y - t)) := by
    intro i y
    simp only
    rw [hf i y, show y + basisVec i - t = (y - t) + basisVec i by abel, hg i]
  have htr := hp.setIntegral_cube_add t
  have e1 : ∀ x, f x * (molK a t * g (x - t)) = molK a t * (f x * g (x - t)) := fun x => by ring
  simp_rw [e1]
  rw [integral_const_mul]
  congr 1
  rw [← htr]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right]
  rw [add_comm t x]
  ring

/-- **Symmetry of mollification**, `L¹` datum against a bounded field. -/
theorem integral_cube_mollify_mul_comm_L1 {a : ℝ} (ha : 0 < a) {f g : Vec 2 → ℝ}
    (hf : IsTorusPeriodic f) (hg : IsTorusPeriodic g)
    (hfl : LocallyIntegrable f volume) (hgl : LocallyIntegrable g volume) {Bg : ℝ}
    (hgB : ∀ᵐ x ∂(volume : Measure (Vec 2)), |g x| ≤ Bg) :
    ∫ x in torusCube, mollify a g x * f x = ∫ x in torusCube, mollify a f x * g x := by
  rw [mollify_pairing_L1 ha hf hfl hg hgl hgB,
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
  rw [show -t + (x + t) = x by abel, add_comm t x]
  ring

end PDE
