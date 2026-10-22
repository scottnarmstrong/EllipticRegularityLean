module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Measure.AxisBoxVolume

/-!
# Axis-cube shell slabs

The shell is covered by the two outer slabs in each coordinate.  Slabs
in distinct coordinates have a common open cube of controlled volume.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The shell between a closed inner cube and an open cube of twice the radius. -/
def cubeShell {d : ℕ} (x₀ : Vec d) (r : ℝ) : Set (Vec d) :=
  centeredAxisCube x₀ (2 * r) \ closedCenteredAxisCube x₀ r

/-- One of the `2d` open slabs covering a cube shell; `true` is the positive side. -/
def cubeShellSlab {d : ℕ} (x₀ : Vec d) (r : ℝ)
    (i : Fin d) (positive : Bool) : Set (Vec d) :=
  axisBox
    (fun j => if j = i then
      (if positive then x₀ j + r else x₀ j - 2 * r)
      else x₀ j - 2 * r)
    (fun j => if j = i then
      (if positive then x₀ j + 2 * r else x₀ j - r)
      else x₀ j + 2 * r)

/-- Every outer slab lies in the shell. -/
theorem cubeShellSlab_subset {d : ℕ} (x₀ : Vec d) (r : ℝ)
    (i : Fin d) (positive : Bool) :
    cubeShellSlab x₀ r i positive ⊆ cubeShell x₀ r := by
  intro x hx
  constructor
  · intro j _
    have hj := hx j (Set.mem_univ j)
    change x₀ j - 2 * r < x j ∧ x j < x₀ j + 2 * r
    by_cases hji : j = i
    · subst j
      cases positive
      · have h := (show x₀ i - 2 * r < x i ∧ x i < x₀ i - r by
          simpa [cubeShellSlab, axisBox] using hj)
        constructor <;> linarith [h.1, h.2]
      · have h := (show x₀ i + r < x i ∧ x i < x₀ i + 2 * r by
          simpa [cubeShellSlab, axisBox] using hj)
        constructor <;> linarith [h.1, h.2]
    · simpa [cubeShellSlab, axisBox, hji] using hj
  · intro hinner
    have hi := hx i (Set.mem_univ i)
    have hinneri := hinner i (Set.mem_univ i)
    change x₀ i - r ≤ x i ∧ x i ≤ x₀ i + r at hinneri
    cases positive
    · have hi' : x₀ i - 2 * r < x i ∧ x i < x₀ i - r := by
        simpa [cubeShellSlab, axisBox] using hi
      exact (not_lt_of_ge hinneri.1) hi'.2
    · have hi' : x₀ i + r < x i ∧ x i < x₀ i + 2 * r := by
        simpa [cubeShellSlab, axisBox] using hi
      exact (not_lt_of_ge hinneri.2) hi'.1

/-- The `2d` outer slabs cover the entire shell. -/
theorem cubeShell_subset_iUnion_slabs {d : ℕ} (x₀ : Vec d) (r : ℝ) :
    cubeShell x₀ r ⊆ ⋃ i : Fin d, ⋃ positive : Bool,
      cubeShellSlab x₀ r i positive := by
  classical
  intro x hx
  have hnot : ¬ ∀ i : Fin d, x₀ i - r ≤ x i ∧ x i ≤ x₀ i + r := by
    intro hall
    exact hx.2 (by
      intro i _
      exact hall i)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have houter : ∀ j : Fin d,
      x₀ j - 2 * r < x j ∧ x j < x₀ j + 2 * r := by
    intro j
    exact hx.1 j (Set.mem_univ j)
  by_cases hneg : x i < x₀ i - r
  · refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨false, ?_⟩⟩
    intro j _
    by_cases hji : j = i
    · subst j
      simpa [cubeShellSlab, axisBox] using
        (show x₀ i - 2 * r < x i ∧ x i < x₀ i - r from ⟨(houter i).1, hneg⟩)
    · simpa [cubeShellSlab, axisBox, hji] using houter j
  · have hpos : x₀ i + r < x i := by
      exact hi (le_of_not_gt hneg)
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨true, ?_⟩⟩
    intro j _
    by_cases hji : j = i
    · subst j
      simpa [cubeShellSlab, axisBox] using
        (show x₀ i + r < x i ∧ x i < x₀ i + 2 * r from ⟨hpos, (houter i).2⟩)
    · simpa [cubeShellSlab, axisBox, hji] using houter j

/-- Each slab is a bounded open convex box. -/
theorem cubeShellSlab_domain {d : ℕ} (x₀ : Vec d) (r : ℝ)
    (i : Fin d) (positive : Bool) :
    IsOpenBoundedConvexDomain (cubeShellSlab x₀ r i positive) :=
  isOpenBoundedConvexDomain_axisBox _ _

/-- A slab at positive radius has a point. -/
theorem cubeShellSlab_nonempty {d : ℕ} (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (i : Fin d) (positive : Bool) :
    (cubeShellSlab x₀ r i positive).Nonempty := by
  apply axisBox_nonempty
  intro j
  by_cases hji : j = i
  · subst j
    cases positive <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> linarith
  · simp only [hji, ite_false]
    linarith

/-- The Euclidean diameter of a slab is at most `4 √d r`. -/
theorem cubeShellSlab_diameter {d : ℕ} (x₀ : Vec d) {r : ℝ}
    (hr : 0 ≤ r) (i : Fin d) (positive : Bool) :
    HasEuclideanDiameterLE (cubeShellSlab x₀ r i positive)
      (Real.sqrt d * (4 * r)) := by
  apply hasEuclideanDiameterLE_axisBox_of_side_le _ _ (by positivity)
  intro j
  by_cases hji : j = i
  · subst j
    cases positive <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> linarith
  · simp only [hji, ite_false]
    ring_nf
    rfl

/-- A slab has no more volume than the outer cube. -/
theorem cubeShellSlab_volume_le {d : ℕ} (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (i : Fin d) (positive : Bool) :
    (volume (cubeShellSlab x₀ r i positive)).toReal ≤ (4 * r) ^ d := by
  have hsub : cubeShellSlab x₀ r i positive ⊆ centeredAxisCube x₀ (2 * r) :=
    fun _ hx => (cubeShellSlab_subset x₀ r i positive hx).1
  calc
    (volume (cubeShellSlab x₀ r i positive)).toReal ≤
        (volume (centeredAxisCube x₀ (2 * r))).toReal := by
      exact ENNReal.toReal_mono
        (volume_centeredAxisCube_ne_top x₀ (2 * r)) (measure_mono hsub)
    _ = (4 * r) ^ d := by
      rw [volume_centeredAxisCube_toReal x₀ (by positivity)]
      congr 1
      ring

/-- A small cube in the intersection of slabs from different coordinates. -/
def cubeShellOverlapCore {d : ℕ} (x₀ : Vec d) (r : ℝ)
    (i j : Fin d) (si sj : Bool) : Set (Vec d) :=
  centeredAxisCube
    (fun k => x₀ k +
      (if k = i then (if si then 3 * r / 2 else -(3 * r / 2))
       else if k = j then (if sj then 3 * r / 2 else -(3 * r / 2))
       else 0)) (r / 4)

private theorem cubeShellOverlapCore_subset_slab_left
    {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (i j : Fin d) (si sj : Bool) :
    cubeShellOverlapCore x₀ r i j si sj ⊆
      cubeShellSlab x₀ r i si := by
  intro x hx k _
  have hk := hx k (Set.mem_univ k)
  by_cases hki : k = i
  · subst k
    have hcenter : x₀ i + (if si then 3 * r / 2 else -(3 * r / 2)) - r / 4 < x i ∧
        x i < x₀ i + (if si then 3 * r / 2 else -(3 * r / 2)) + r / 4 := by
      simpa [cubeShellOverlapCore, centeredAxisCube, axisBox] using hk
    cases si
    · simp only [ite_true, Bool.false_eq_true, ite_false, Set.mem_Ioo]
      simp only [Bool.false_eq_true, ite_false] at hcenter
      constructor <;> linarith [hcenter.1, hcenter.2]
    · simp only [ite_true, Set.mem_Ioo]
      simp only [ite_true] at hcenter
      constructor <;> linarith [hcenter.1, hcenter.2]
  · have hcore : x₀ k +
        (if k = j then (if sj then 3 * r / 2 else -(3 * r / 2)) else 0) - r / 4 < x k ∧
        x k < x₀ k +
        (if k = j then (if sj then 3 * r / 2 else -(3 * r / 2)) else 0) + r / 4 := by
      simpa [cubeShellOverlapCore, centeredAxisCube, axisBox, hki] using hk
    have houter : x₀ k - 2 * r < x k ∧ x k < x₀ k + 2 * r := by
      by_cases hkj : k = j
      · subst k
        cases sj <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hcore <;>
          constructor <;> linarith [hcore.1, hcore.2]
      · simp only [hkj, ite_false] at hcore
        constructor <;> linarith [hcore.1, hcore.2]
    simpa [cubeShellSlab, axisBox, hki] using houter

/-- The controlled core cube lies in both slabs. -/
theorem cubeShellOverlapCore_subset_inter
    {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (i j : Fin d) (hij : i ≠ j) (si sj : Bool) :
    cubeShellOverlapCore x₀ r i j si sj ⊆
      cubeShellSlab x₀ r i si ∩ cubeShellSlab x₀ r j sj := by
  intro x hx
  refine ⟨cubeShellOverlapCore_subset_slab_left x₀ hr i j si sj hx, ?_⟩
  have hswap : cubeShellOverlapCore x₀ r i j si sj =
      cubeShellOverlapCore x₀ r j i sj si := by
    unfold cubeShellOverlapCore
    congr 1
    funext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij.symm]
      · simp [hki, hkj]
  rw [hswap] at hx
  exact cubeShellOverlapCore_subset_slab_left x₀ hr j i sj si hx

/-- Slabs on distinct coordinate axes overlap in volume by at least `(r/2)^d`. -/
theorem cubeShellSlab_inter_volume_lower
    {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (i j : Fin d) (hij : i ≠ j) (si sj : Bool) :
    (r / 2) ^ d ≤
      (volume (cubeShellSlab x₀ r i si ∩ cubeShellSlab x₀ r j sj)).toReal := by
  have hsub := cubeShellOverlapCore_subset_inter x₀ hr i j hij si sj
  have hfin : volume (cubeShellSlab x₀ r i si ∩
      cubeShellSlab x₀ r j sj) ≠ ∞ :=
    measure_ne_top_of_subset Set.inter_subset_left (volume_axisBox_ne_top _ _)
  have hvol := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [cubeShellOverlapCore, volume_centeredAxisCube_toReal _ (by positivity)] at hvol
  convert hvol using 1
  congr 1
  ring

end PDE
