module

public import PDEFoundation.Measure.DyadicBoxMaximal

/-! # The actual single-box sparse pairing estimate -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- A measurable three-quarter remainder and an actual coefficient minorant
give the single-box pairing bound. The maximal average domination is proved
from the literal containing descendant. -/
theorem single_sparse_pairing_le
    {d : ℕ} (I : Box (Fin d)) (p : List (Set (Fin d)))
    (b φ : Vec d → ℝ) (a : ℝ) (E : Set (Vec d)) (hE : MeasurableSet E)
    (hsub : E ⊆ (dyadicDescendant I p : Set (Vec d)))
    (hpacking : ENNReal.ofReal (3 / 4 : ℝ) *
      volume (dyadicDescendant I p : Set (Vec d)) ≤ volume E)
    (hminor : ∀ᵐ x ∂volume.restrict (dyadicDescendant I p : Set (Vec d)), a ≤ |b x|) :
    ENNReal.ofReal a *
        (∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |φ x|) ≤
      ENNReal.ofReal (4 / 3 : ℝ) *
        ∫⁻ x in E, ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x := by
  let v := volume (dyadicDescendant I p : Set (Vec d))
  let A := dyadicBoxAverage I φ p
  have hvTop : v ≠ ⊤ := (volume_dyadicDescendant_lt_top I p).ne
  have hvReal : 0 < v.toReal := by
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ =>
      sub_pos.mpr ((dyadicDescendant I p).lower_lt_upper i)
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv, ENNReal.toReal_zero] at hvReal
    exact (lt_self_iff_false 0).mp hvReal
  have hnormalization : A * v =
      ∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |φ x| := by
    dsimp only [A, dyadicBoxAverage]
    change (v⁻¹ * _) * v = _
    rw [mul_right_comm, ENNReal.inv_mul_cancel hv0 hvTop, one_mul]
  have hvBound : v ≤ ENNReal.ofReal (4 / 3 : ℝ) * volume E := by
    have h := mul_le_mul_right hpacking (ENNReal.ofReal (4 / 3 : ℝ))
    have hfactor : ENNReal.ofReal (4 / 3 : ℝ) * ENNReal.ofReal (3 / 4 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3)]
      norm_num
    rw [← mul_assoc, hfactor, one_mul] at h
    exact h
  have hminorE : ∀ᵐ x ∂volume.restrict E, a ≤ |b x| :=
    ae_restrict_of_ae_restrict_of_subset hsub hminor
  have hpoint : ∀ᵐ x ∂volume.restrict E,
      ENNReal.ofReal a * A ≤ ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x := by
    filter_upwards [hminorE, ae_restrict_mem hE] with x ha hx
    exact mul_le_mul (ENNReal.ofReal_le_ofReal ha)
      (dyadicBoxAverage_le_dyadicBoxMaximal I φ p (hsub hx)) (zero_le) (zero_le)
  have hIntegral : (ENNReal.ofReal a * A) * volume E ≤
      ∫⁻ x in E, ENNReal.ofReal |b x| * dyadicBoxMaximal I φ x := by
    have h := lintegral_mono_ae hpoint
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  calc
    ENNReal.ofReal a *
        (∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |φ x|) =
        (ENNReal.ofReal a * A) * v := by rw [← hnormalization, mul_assoc]
    _ ≤ (ENNReal.ofReal a * A) * (ENNReal.ofReal (4 / 3 : ℝ) * volume E) :=
      mul_le_mul_right hvBound _
    _ = ENNReal.ofReal (4 / 3 : ℝ) * ((ENNReal.ofReal a * A) * volume E) := by ac_rfl
    _ ≤ _ := mul_le_mul_right hIntegral _

end PDE
