module

public import PDEFoundation.Geometry.DyadicBoxAtPoint
public import PDEFoundation.Geometry.DyadicBoxVolumeRatio
public import PDEFoundation.Sobolev.Mean

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Absolute deviation of a scalar integral average is bounded by the average
absolute deviation. -/
theorem abs_integralAverage_sub_le_integralAverage_abs_sub
    {U : Set (Vec d)} {f : Vec d → ℝ} (c : ℝ)
    (hf : IntegrableOn f U volume) (hUpos : 0 < volume U)
    (hUtop : volume U < ∞) :
    |integralAverage U f - c| ≤
      integralAverage U (fun y => |f y - c|) := by
  have hV : 0 < (volume U).toReal :=
    ENNReal.toReal_pos hUpos.ne' hUtop.ne
  have hc : IntegrableOn (fun _y : Vec d => c) U volume :=
    integrableOn_const hUtop.ne
  have hsub : IntegrableOn (fun y => f y - c) U volume := hf.sub hc
  have hintSub : (∫ y in U, f y - c ∂volume) =
      (∫ y in U, f y ∂volume) - (volume U).toReal * c := by
    rw [integral_sub hf hc, setIntegral_const]
    rfl
  unfold integralAverage
  have hid : (volume U).toReal⁻¹ * (∫ y in U, f y ∂volume) - c =
      (volume U).toReal⁻¹ *
        ((∫ y in U, f y ∂volume) - (volume U).toReal * c) := by
    field_simp
  rw [hid, ← hintSub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hV.le)]
  exact mul_le_mul_of_nonneg_left
    abs_integral_le_integral_abs (inv_nonneg.mpr hV.le)

/-- A nonnegative average on the selected dyadic descendant is controlled by
the average on its containing closed supremum cube. -/
theorem integralAverage_dyadicBoxAtDepth_le_closedBall
    (I : Box (Fin d)) (x : Vec d) (hx : x ∈ (I : Set (Vec d)))
    (n : ℕ) (hd : 0 < d) {h : Vec d → ℝ}
    (hInt : IntegrableOn h
      (Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n)) volume)
    (hNonneg : 0 ≤ᵐ[volume.restrict
      (Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n))] h) :
    integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) h ≤
      ((2 * ‖I.upper - I.lower‖) ^ d /
        (volume (I : Set (Vec d))).toReal) *
      integralAverage
        (Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n)) h := by
  let Q : Set (Vec d) := dyadicBoxAtDepth I x hx n
  let B : Set (Vec d) :=
    Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n)
  let C : ℝ := (2 * ‖I.upper - I.lower‖) ^ d /
    (volume (I : Set (Vec d))).toReal
  have hQB : Q ⊆ B := dyadicBoxAtDepth_subset_closedBall I x hx n
  have hQInt : IntegrableOn h Q volume := hInt.mono_set hQB
  have hIntLe : (∫ y in Q, h y ∂volume) ≤ ∫ y in B, h y ∂volume :=
    setIntegral_mono_set hInt hNonneg (ae_of_all volume fun y hy => hQB hy)
  have hQpos : 0 < (volume Q).toReal := by
    exact volume_box_toReal_pos (dyadicBoxAtDepth I x hx n)
  have hr := dyadicBoxAtDepth_radius_pos I hd n
  have hBpos : 0 < (volume B).toReal := by
    dsimp only [B]
    rw [Real.volume_pi_closedBall x hr.le, ENNReal.toReal_ofReal]
    · positivity
    · positivity
  have hratio : (volume B).toReal = C * (volume Q).toReal := by
    have h := volume_closedBall_dyadicDescendant_ratio I
      (dyadicPathAtDepth I x hx n) x (mem_dyadicBoxAtDepth I x hx n) hd
    rw [length_dyadicPathAtDepth I x hx n] at h
    exact h
  have hCpos : 0 < C := by
    dsimp only [C]
    exact div_pos (pow_pos (mul_pos zero_lt_two
      (norm_upper_sub_lower_pos I hd)) _) (volume_box_toReal_pos I)
  have hcoeff : (volume Q).toReal⁻¹ = C * (volume B).toReal⁻¹ := by
    rw [hratio]
    rw [mul_inv]
    field_simp
  change (volume Q).toReal⁻¹ * (∫ y in Q, h y ∂volume) ≤
    C * ((volume B).toReal⁻¹ * ∫ y in B, h y ∂volume)
  rw [hcoeff, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hIntLe (inv_nonneg.mpr hBpos.le)) hCpos.le

/-- Pointwise nonnegativity convenience form of the dyadic average
comparison. -/
theorem integralAverage_dyadicBoxAtDepth_le_closedBall_of_nonneg
    (I : Box (Fin d)) (x : Vec d) (hx : x ∈ (I : Set (Vec d)))
    (n : ℕ) (hd : 0 < d) {h : Vec d → ℝ}
    (hInt : IntegrableOn h
      (Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n)) volume)
    (hNonneg : ∀ y, y ∈ Metric.closedBall x
      (‖I.upper - I.lower‖ / (2 : ℝ) ^ n) → 0 ≤ h y) :
    integralAverage (dyadicBoxAtDepth I x hx n : Set (Vec d)) h ≤
      ((2 * ‖I.upper - I.lower‖) ^ d /
        (volume (I : Set (Vec d))).toReal) *
      integralAverage
        (Metric.closedBall x (‖I.upper - I.lower‖ / (2 : ℝ) ^ n)) h := by
  apply integralAverage_dyadicBoxAtDepth_le_closedBall I x hx n hd hInt
  exact ae_restrict_of_forall_mem measurableSet_closedBall hNonneg

end

end PDE
