module

public import PDEFoundation.Geometry.AxisCube
public import Mathlib.Analysis.BoxIntegral.Box.SubboxInduction
public import Mathlib.Analysis.BoxIntegral.Partition.Measure

/-!
# Literal dyadic descendants of a box

This file records the reusable geometry of repeated center splitting. A
descendant is indexed by a literal finite list of child choices; no child or
ancestor is selected by choice.
-/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- The dyadic descendant obtained by repeatedly splitting a box through its
coordinate center. Each set `s : Set (Fin d)` chooses one of the `2 ^ d`
children at that step. -/
noncomputable def dyadicDescendant {d : ℕ} (I : Box (Fin d)) :
    List (Set (Fin d)) → Box (Fin d)
  | [] => I
  | s :: ss => dyadicDescendant (I.splitCenterBox s) ss

@[simp]
theorem dyadicDescendant_nil {d : ℕ} (I : Box (Fin d)) :
    dyadicDescendant I [] = I :=
  rfl

@[simp]
theorem dyadicDescendant_cons {d : ℕ} (I : Box (Fin d))
    (s : Set (Fin d)) (ss : List (Set (Fin d))) :
    dyadicDescendant I (s :: ss) =
      dyadicDescendant (I.splitCenterBox s) ss :=
  rfl

/-- Following an appended path is the same as first following its prefix and
then following its suffix. -/
theorem dyadicDescendant_append {d : ℕ} (I : Box (Fin d))
    (p q : List (Set (Fin d))) :
    dyadicDescendant I (p ++ q) =
      dyadicDescendant (dyadicDescendant I p) q := by
  induction p generalizing I with
  | nil => rfl
  | cons s ss ih =>
      exact ih (I.splitCenterBox s)

/-- Every literal dyadic descendant is contained in its root box. -/
theorem dyadicDescendant_le {d : ℕ} (I : Box (Fin d))
    (p : List (Set (Fin d))) :
    dyadicDescendant I p ≤ I := by
  induction p generalizing I with
  | nil => exact le_rfl
  | cons s ss ih =>
      exact (ih (I.splitCenterBox s)).trans (I.splitCenterBox_le s)

/-- Each center split halves every coordinate width. -/
theorem upper_sub_lower_dyadicDescendant {d : ℕ}
    (I : Box (Fin d)) (p : List (Set (Fin d))) (i : Fin d) :
    (dyadicDescendant I p).upper i -
        (dyadicDescendant I p).lower i =
      (I.upper i - I.lower i) / (2 : ℝ) ^ p.length := by
  induction p generalizing I with
  | nil => simp only [dyadicDescendant_nil, List.length_nil, pow_zero, div_one]
  | cons s ss ih =>
      rw [dyadicDescendant_cons, ih,
        I.upper_sub_lower_splitCenterBox s i, List.length_cons, pow_succ]
      ring

/-- A dyadic descendant is Lebesgue measurable. -/
theorem measurableSet_dyadicDescendant {d : ℕ}
    (I : Box (Fin d)) (p : List (Set (Fin d))) :
    MeasurableSet (dyadicDescendant I p : Set (Vec d)) :=
  (dyadicDescendant I p).measurableSet_coe

/-- A dyadic descendant has finite Lebesgue volume. -/
theorem volume_dyadicDescendant_lt_top {d : ℕ}
    (I : Box (Fin d)) (p : List (Set (Fin d))) :
    volume (dyadicDescendant I p : Set (Vec d)) < ∞ :=
  (dyadicDescendant I p).measure_coe_lt_top volume

/-- A box with a common coordinate width is its native open axis cube. -/
theorem Ioo_eq_axisCube_of_forall_upper_sub_lower_eq {d : ℕ}
    (I : Box (Fin d)) (L : ℝ)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    Box.Ioo I = axisCube I.lower L := by
  ext x
  constructor
  · intro hx i _
    have hxi := hx i (Set.mem_univ i)
    exact ⟨hxi.1, by linarith [hxi.2, hwidth i]⟩
  · intro hx i _
    have hxi := hx i (Set.mem_univ i)
    exact ⟨hxi.1, by linarith [hxi.2, hwidth i]⟩

/-- The half-open box carrier agrees almost everywhere with the native open
axis cube when all coordinate widths are equal. -/
theorem coe_ae_eq_axisCube_of_forall_upper_sub_lower_eq {d : ℕ}
    (I : Box (Fin d)) (L : ℝ)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    (I : Set (Vec d)) =ᵐ[volume] axisCube I.lower L := by
  rw [← Ioo_eq_axisCube_of_forall_upper_sub_lower_eq I L hwidth]
  exact I.coe_ae_eq_Icc.trans I.Ioo_ae_eq_Icc.symm

end PDE
