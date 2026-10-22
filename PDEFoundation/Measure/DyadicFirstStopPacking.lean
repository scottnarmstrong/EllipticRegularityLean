module

public import PDEFoundation.Measure.DyadicBoxMaximalWeak
public import PDEFoundation.Sobolev.Mean

/-! # Packing of first dyadic stopping boxes -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

/-- First descendants whose absolute average exceeds four times the root
average occupy at most one quarter of the root box. -/
theorem volume_iUnion_firstPrefixStop_dyadicBoxAverage_le
    {d : ℕ} (I : Box (Fin d)) (b : Vec d → ℝ)
    (hb : IntegrableOn b (I : Set (Vec d)))
    (havg : 0 < integralAverage (I : Set (Vec d)) fun x => |b x|) :
    volume (⋃ p : List (Set (Fin d)),
      ⋃ (_ : IsFirstPrefixStop
        (fun q => ENNReal.ofReal
          (4 * integralAverage (I : Set (Vec d)) fun x => |b x|) <
            dyadicBoxAverage I b q) p),
        (dyadicDescendant I p : Set (Vec d))) ≤
      (4 : ℝ≥0∞)⁻¹ * volume (I : Set (Vec d)) := by
  let A := integralAverage (I : Set (Vec d)) fun x => |b x|
  let E := {x | ENNReal.ofReal (4 * A) < dyadicBoxMaximal I b x}
  have hunion : (⋃ p : List (Set (Fin d)),
      ⋃ (_ : IsFirstPrefixStop
        (fun q => ENNReal.ofReal (4 * A) < dyadicBoxAverage I b q) p),
        (dyadicDescendant I p : Set (Vec d))) = E := by
    exact (set_lt_dyadicBoxMaximal_eq_firstStops I b (ENNReal.ofReal (4 * A))).symm
  rw [show integralAverage (I : Set (Vec d)) (fun x => |b x|) = A from rfl, hunion]
  have hweak := ofReal_mul_volume_set_lt_dyadicBoxMaximal_le_lintegral
    I b (4 * A)
  have hE : E ⊆ (I : Set (Vec d)) := by
    intro x hx
    by_contra hxI
    have hz := dyadicBoxMaximal_eq_zero_of_notMem I b hxI
    change ENNReal.ofReal (4 * A) < dyadicBoxMaximal I b x at hx
    rw [hz] at hx
    exact (not_lt_of_ge (zero_le)) hx
  have hmono : (∫⁻ x in E, ENNReal.ofReal |b x|) ≤
      ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal |b x| :=
    lintegral_mono_set hE
  have hroot : (∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal |b x|) =
      ENNReal.ofReal A * volume (I : Set (Vec d)) := by
    have hvTop := I.measure_coe_lt_top volume
    have hvReal : 0 < (volume (I : Set (Vec d))).toReal := by
      rw [Box.volume_apply']
      exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)
    have hint : ∫ x in (I : Set (Vec d)), |b x| =
        A * (volume (I : Set (Vec d))).toReal := by
      dsimp [A, integralAverage]
      field_simp
    rw [← ofReal_integral_eq_lintegral_ofReal hb.abs
      (ae_of_all _ fun x => abs_nonneg (b x)), hint,
      ENNReal.ofReal_mul havg.le,
      ENNReal.ofReal_toReal hvTop.ne]
  have hmain : ENNReal.ofReal (4 * A) * volume E ≤
      ENNReal.ofReal A * volume (I : Set (Vec d)) := hweak.trans hmono |>.trans_eq hroot
  have hA0 : ENNReal.ofReal A ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr havg
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hmain
  have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by norm_num
  rw [h4] at hmain
  have hfactored : ENNReal.ofReal A * ((4 : ℝ≥0∞) * volume E) ≤
      ENNReal.ofReal A * volume (I : Set (Vec d)) := by
    calc
      ENNReal.ofReal A * ((4 : ℝ≥0∞) * volume E) =
          (4 : ℝ≥0∞) * (ENNReal.ofReal A * volume E) := by ac_rfl
      _ ≤ ENNReal.ofReal A * volume (I : Set (Vec d)) := by
        simpa only [mul_assoc] using hmain
  have hcancel := (ENNReal.mul_le_mul_iff_right hA0 ENNReal.ofReal_ne_top).mp hfactored
  have hdiv : volume E ≤ volume (I : Set (Vec d)) / (4 : ℝ≥0∞) :=
    (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
      (by simpa [mul_comm] using hcancel)
  simpa [ENNReal.div_eq_inv_mul] using hdiv

end PDE
