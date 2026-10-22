module

public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

/-!
# Comparing a field with an oscillation-decaying replacement

This is the elementary mean-square comparison used after harmonic replacement.
The contraction premise is explicitly a premise of this generic lemma; the
harmonic theorem supplying it is a separate analytic result.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Comparison of centered oscillations, with the exact volume-ratio loss
on the replacement error. -/
theorem centeredVectorMeanL2_comparison_of_contraction
    {V U : Set (Vec d)} (hVU : V ⊆ U)
    {h w : Vec d → Vec d}
    (hh : MemVectorL2On U h) (hw : MemVectorL2On U w)
    (hVpos : 0 < volume V) (hVtop : volume V < ∞)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hdecay : centeredVectorMeanL2 V h ≤ θ * centeredVectorMeanL2 U h) :
    centeredVectorMeanL2 V (fun x => h x + w x) ≤
      θ * centeredVectorMeanL2 U (fun x => h x + w x) +
        (θ + Real.sqrt ((volume U).toReal / (volume V).toReal)) *
          Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) := by
  have hhV : MemVectorL2On V h := fun i =>
    (hh i).mono_measure (Measure.restrict_mono hVU le_rfl)
  have hwV : MemVectorL2On V w := fun i =>
    (hw i).mono_measure (Measure.restrict_mono hVU le_rfl)
  have hsum : MemVectorL2On U (fun x => h x + w x) := fun i =>
    (hh i).add (hw i)
  have hneg : MemVectorL2On U (fun x => -w x) := fun i => (hw i).neg
  have hnegEnergy :
      Real.sqrt (integralAverage U (fun x => vecNormSq (-w x))) =
        Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) := by
    simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]
  have hreverse : centeredVectorMeanL2 U h ≤
      centeredVectorMeanL2 U (fun x => h x + w x) +
        Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) := by
    have htri := centeredVectorMeanL2_add_le hsum hneg hUtop
    have hcancel : (fun x => h x + w x + -w x) = h := by
      funext x
      exact add_neg_cancel_right (h x) (w x)
    rw [hcancel] at htri
    exact htri.trans (add_le_add le_rfl
      ((centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq hneg hUpos hUtop).trans_eq
        hnegEnergy))
  have hwbound : centeredVectorMeanL2 V w ≤
      Real.sqrt ((volume U).toReal / (volume V).toReal) *
        Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) :=
    (centeredVectorMeanL2_mono_set hVU hw hVpos hVtop hUpos hUtop).trans
      (mul_le_mul_of_nonneg_left
        (centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq hw hUpos hUtop)
        (Real.sqrt_nonneg _))
  calc
    centeredVectorMeanL2 V (fun x => h x + w x) ≤
        centeredVectorMeanL2 V h + centeredVectorMeanL2 V w :=
      centeredVectorMeanL2_add_le hhV hwV hVtop
    _ ≤ θ * centeredVectorMeanL2 U h +
        Real.sqrt ((volume U).toReal / (volume V).toReal) *
          Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) :=
      add_le_add hdecay hwbound
    _ ≤ θ * (centeredVectorMeanL2 U (fun x => h x + w x) +
          Real.sqrt (integralAverage U (fun x => vecNormSq (w x)))) +
        Real.sqrt ((volume U).toReal / (volume V).toReal) *
          Real.sqrt (integralAverage U (fun x => vecNormSq (w x))) :=
      add_le_add (mul_le_mul_of_nonneg_left hreverse hθ) le_rfl
    _ = _ := by ring

end PDE
