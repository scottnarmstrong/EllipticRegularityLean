module

public import PDEFoundation.Measure.DyadicBoxMaximal
public import Mathlib.MeasureTheory.Function.EssSup

/-! # Essential infima on literal dyadic descendants -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- The literal Mathlib essential infimum of the extended absolute value on a
dyadic descendant. -/
noncomputable def dyadicBoxEssentialInf {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal |b x|)
    (volume.restrict (dyadicDescendant I p : Set (Vec d)))

theorem ae_dyadicBoxEssentialInf_le {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) :
    ∀ᵐ x ∂volume.restrict (dyadicDescendant I p : Set (Vec d)),
      dyadicBoxEssentialInf I b p ≤ ENNReal.ofReal |b x| := by
  exact ae_essInf_le

theorem dyadicBoxEssentialInf_ne_top {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) :
    dyadicBoxEssentialInf I b p ≠ ⊤ := by
  let Q : Set (Vec d) := (dyadicDescendant I p : Set (Vec d))
  have hQpos : 0 < volume Q := by
    apply (ENNReal.toReal_pos_iff.mp ?_).1
    dsimp [Q]
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ =>
      sub_pos.mpr ((dyadicDescendant I p).lower_lt_upper i)
  have hμ : volume.restrict Q ≠ 0 := by
    intro hz
    have hu := congrArg (fun μ : Measure (Vec d) => μ Set.univ) hz
    have hQmeas : MeasurableSet Q := measurableSet_dyadicDescendant I p
    have hQzero : volume Q = 0 := by
      simpa [Measure.restrict_apply, hQmeas] using hu
    exact hQpos.ne' hQzero
  let : (ae (volume.restrict Q)).NeBot := ae_neBot.mpr hμ
  obtain ⟨x, hx⟩ :=
    (ae_dyadicBoxEssentialInf_le I b p).exists
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx

/-- The finite real representative of the essential infimum. -/
noncomputable def dyadicBoxEssentialInfReal {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) : ℝ :=
  (dyadicBoxEssentialInf I b p).toReal

/-- Re-embedding the real coefficient recovers the literal essential infimum;
the proved finiteness guard prevents loss of infinite values. -/
@[simp]
theorem ofReal_dyadicBoxEssentialInfReal {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) :
    ENNReal.ofReal (dyadicBoxEssentialInfReal I b p) = dyadicBoxEssentialInf I b p :=
  ENNReal.ofReal_toReal (dyadicBoxEssentialInf_ne_top I b p)

theorem dyadicBoxEssentialInfReal_nonneg {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) :
    0 ≤ dyadicBoxEssentialInfReal I b p :=
  ENNReal.toReal_nonneg

theorem ae_dyadicBoxEssentialInfReal_le {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) :
    ∀ᵐ x ∂volume.restrict (dyadicDescendant I p : Set (Vec d)),
      dyadicBoxEssentialInfReal I b p ≤ |b x| := by
  filter_upwards [ae_dyadicBoxEssentialInf_le I b p] with x hx
  unfold dyadicBoxEssentialInfReal
  rw [← ENNReal.toReal_ofReal (abs_nonneg (b x))]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hx

theorem dyadicBoxEssentialInf_eq_essInf_of_ae_nonneg {d : ℕ}
    (I : Box (Fin d)) (b : Vec d → ℝ) (p : List (Set (Fin d)))
    (hb : ∀ᵐ x ∂volume.restrict (dyadicDescendant I p : Set (Vec d)), 0 ≤ b x) :
    dyadicBoxEssentialInf I b p =
      essInf (fun x => ENNReal.ofReal (b x))
        (volume.restrict (dyadicDescendant I p : Set (Vec d))) := by
  unfold dyadicBoxEssentialInf
  apply essInf_congr_ae
  filter_upwards [hb] with x hx
  rw [abs_of_nonneg hx]

end PDE
