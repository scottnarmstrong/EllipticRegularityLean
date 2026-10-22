module

public import PDEFoundation.Geometry.DyadicBoxVolume
public import PDEFoundation.Sobolev.Mean

/-! # Normalized averages on center-split children -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory

/-- A nonnegative average on a center-split child is at most `2 ^ d` times
the corresponding parent average. -/
theorem integralAverage_splitCenterBox_le_pow_mul
    {d : ℕ} (I : Box (Fin d)) (s : Set (Fin d))
    (h : Vec d → ℝ) (hh : IntegrableOn h (I : Set (Vec d)))
    (hnonneg : ∀ᵐ x ∂volume.restrict (I : Set (Vec d)), 0 ≤ h x) :
    integralAverage (I.splitCenterBox s : Set (Vec d)) h ≤
      (2 : ℝ) ^ d * integralAverage (I : Set (Vec d)) h := by
  have hsub : (I.splitCenterBox s : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
    I.splitCenterBox_le s
  have hint : (∫ x in (I.splitCenterBox s : Set (Vec d)), h x ∂volume) ≤
      ∫ x in (I : Set (Vec d)), h x ∂volume :=
    setIntegral_mono_set hh hnonneg (ae_of_all _ hsub)
  have hvParent : 0 < (volume (I : Set (Vec d))).toReal := by
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)
  have hvChild : 0 < (volume (I.splitCenterBox s : Set (Vec d))).toReal := by
    rw [volume_splitCenterBox_toReal]
    positivity
  unfold integralAverage
  rw [volume_splitCenterBox_toReal]
  calc
    ((volume (I : Set (Vec d))).toReal / (2 : ℝ) ^ d)⁻¹ *
        ∫ x in (I.splitCenterBox s : Set (Vec d)), h x ∂volume ≤
      ((volume (I : Set (Vec d))).toReal / (2 : ℝ) ^ d)⁻¹ *
        ∫ x in (I : Set (Vec d)), h x ∂volume :=
      mul_le_mul_of_nonneg_left hint
        (inv_nonneg.mpr (div_nonneg hvParent.le (by positivity)))
    _ = (2 : ℝ) ^ d *
        ((volume (I : Set (Vec d))).toReal⁻¹ *
          ∫ x in (I : Set (Vec d)), h x ∂volume) := by
      field_simp

end PDE
