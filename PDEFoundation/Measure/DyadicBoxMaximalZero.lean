module

public import PDEFoundation.Measure.DyadicBoxMaximal
public import PDEFoundation.Sobolev.Mean

/-! # Vanishing of the dyadic maximal function at zero root energy -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

/-- A zero absolute average on the root forces the input to vanish almost
everywhere on that box. -/
theorem ae_eq_zero_on_box_of_integralAverage_abs_eq_zero
    {d : ℕ} (I : Box (Fin d)) (b : Vec d → ℝ)
    (hb : IntegrableOn b (I : Set (Vec d)))
    (havg : integralAverage (I : Set (Vec d)) (fun x => |b x|) = 0) :
    b =ᵐ[volume.restrict (I : Set (Vec d))] 0 := by
  have hvReal : 0 < (volume (I : Set (Vec d))).toReal := by
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)
  have hint : ∫ x in (I : Set (Vec d)), |b x| = 0 := by
    unfold integralAverage at havg
    rcases mul_eq_zero.mp havg with hinv | hint
    · exact (inv_ne_zero hvReal.ne' hinv).elim
    · exact hint
  have habs : (fun x => |b x|) =ᵐ[volume.restrict (I : Set (Vec d))] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun x => abs_nonneg (b x)) hb.abs).mp hint
  filter_upwards [habs] with x hx
  exact abs_eq_zero.mp hx

/-- If the root absolute average is zero, every literal descendant average
and hence the dyadic maximal function vanish everywhere, including off the
root box. -/
theorem dyadicBoxMaximal_eq_zero_of_integralAverage_abs_eq_zero
    {d : ℕ} (I : Box (Fin d)) (b : Vec d → ℝ)
    (hb : IntegrableOn b (I : Set (Vec d)))
    (havg : integralAverage (I : Set (Vec d)) (fun x => |b x|) = 0) :
    ∀ x, dyadicBoxMaximal I b x = 0 := by
  have hvReal : 0 < (volume (I : Set (Vec d))).toReal := by
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)
  have hint : ∫ x in (I : Set (Vec d)), |b x| = 0 := by
    unfold integralAverage at havg
    rcases mul_eq_zero.mp havg with hinv | hint
    · exact (inv_ne_zero hvReal.ne' hinv).elim
    · exact hint
  have hroot : (∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal |b x|) = 0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hb.abs
      (ae_of_all _ fun x => abs_nonneg (b x)), hint, ENNReal.ofReal_zero]
  have hdesc (p : List (Set (Fin d))) :
      (∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |b x|) = 0 := by
    apply le_zero_iff.mp
    exact (lintegral_mono_set (dyadicDescendant_le I p)).trans_eq hroot
  have havgDesc (p : List (Set (Fin d))) : dyadicBoxAverage I b p = 0 := by
    unfold dyadicBoxAverage
    rw [hdesc p, mul_zero]
  intro x
  unfold dyadicBoxMaximal
  apply le_antisymm
  · apply iSup_le
    intro p
    apply iSup_le
    intro _
    rw [havgDesc p]
  · exact zero_le

end PDE
