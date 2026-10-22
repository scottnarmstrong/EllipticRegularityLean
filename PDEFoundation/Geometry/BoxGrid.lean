module

public import PDEFoundation.Geometry.BoxCenter
public import Mathlib.Analysis.BoxIntegral.UnitPartition

/-! # A countable grid of equal-side half-open boxes -/

@[expose] public section

namespace PDE

open BoxIntegral Set

/-- The half-open grid box of side length `L` at integer index `k`. -/
def boxGrid {d : ℕ} (L : ℝ) (hL : 0 < L) (k : Fin d → ℤ) : Box (Fin d) where
  lower i := (k i : ℝ) * L
  upper i := ((k i : ℝ) + 1) * L
  lower_lt_upper i := by nlinarith

@[simp]
theorem boxGrid_lower {d : ℕ} (L : ℝ) (hL : 0 < L)
    (k : Fin d → ℤ) (i : Fin d) :
    (boxGrid L hL k).lower i = (k i : ℝ) * L :=
  rfl

@[simp]
theorem boxGrid_upper {d : ℕ} (L : ℝ) (hL : 0 < L)
    (k : Fin d → ℤ) (i : Fin d) :
    (boxGrid L hL k).upper i = ((k i : ℝ) + 1) * L :=
  rfl

/-- The literal integer index of the unique grid box containing `x`. -/
noncomputable def boxGridIndex {d : ℕ} (L : ℝ) (x : Vec d) : Fin d → ℤ :=
  fun i => ⌈x i / L⌉ - 1

@[simp]
theorem boxGridIndex_apply {d : ℕ} (L : ℝ) (x : Vec d) (i : Fin d) :
    boxGridIndex L x i = ⌈x i / L⌉ - 1 :=
  rfl

/-- Membership in a grid box is characterized exactly by the ceiling index. -/
theorem mem_boxGrid_iff_index {d : ℕ} {L : ℝ} (hL : 0 < L)
    {k : Fin d → ℤ} {x : Vec d} :
    x ∈ boxGrid L hL k ↔ boxGridIndex L x = k := by
  rw [Box.mem_def]
  simp_rw [boxGrid_lower, boxGrid_upper, Set.mem_Ioc, funext_iff,
    boxGridIndex_apply]
  apply forall_congr'
  intro i
  rw [sub_eq_iff_eq_add, Int.ceil_eq_iff]
  push_cast
  constructor <;> rintro ⟨hlo, hhi⟩
  · norm_num at hlo hhi ⊢
    constructor
    · exact (lt_div_iff₀ hL).2 (by simpa only [mul_comm] using hlo)
    · exact (div_le_iff₀ hL).2 (by simpa only [mul_comm] using hhi)
  · norm_num at hlo hhi ⊢
    constructor
    · exact (lt_div_iff₀ hL).1 (by simpa only [mul_comm] using hlo)
    · exact (div_le_iff₀ hL).1 (by simpa only [mul_comm] using hhi)

/-- Every point belongs to the grid box selected by its literal index. -/
theorem mem_boxGrid_index {d : ℕ} {L : ℝ} (hL : 0 < L) (x : Vec d) :
    x ∈ boxGrid L hL (boxGridIndex L x) :=
  mem_boxGrid_iff_index hL |>.2 rfl

/-- Every point belongs to a unique grid box. -/
theorem existsUnique_mem_boxGrid {d : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Vec d) : ∃! k : Fin d → ℤ, x ∈ boxGrid L hL k := by
  refine ⟨boxGridIndex L x, mem_boxGrid_index hL x, ?_⟩
  intro k hk
  exact (mem_boxGrid_iff_index hL).1 hk |>.symm

/-- The half-open grid boxes cover the whole native vector space. -/
theorem iUnion_boxGrid {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (⋃ k : Fin d → ℤ, (boxGrid L hL k : Set (Vec d))) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨boxGridIndex L x, mem_boxGrid_index hL x⟩

/-- Distinct grid indices have disjoint half-open box carriers. -/
theorem disjoint_boxGrid {d : ℕ} {L : ℝ} (hL : 0 < L)
    {k l : Fin d → ℤ} (hkl : k ≠ l) :
    Disjoint (boxGrid L hL k : Set (Vec d)) (boxGrid L hL l : Set (Vec d)) := by
  apply Set.disjoint_left.mpr
  intro x hxk hxl
  exact hkl ((mem_boxGrid_iff_index hL).1 hxk |>.symm.trans
    ((mem_boxGrid_iff_index hL).1 hxl))

/-- The entire grid family is pairwise disjoint. -/
theorem pairwiseDisjoint_boxGrid {d : ℕ} {L : ℝ} (hL : 0 < L) :
    Pairwise fun k l : Fin d → ℤ =>
      Disjoint (boxGrid L hL k : Set (Vec d)) (boxGrid L hL l : Set (Vec d)) :=
  fun _ _ hkl => disjoint_boxGrid hL hkl

/-- Distinct grid boxes also have disjoint open interiors. -/
theorem disjoint_boxGrid_Ioo {d : ℕ} {L : ℝ} (hL : 0 < L)
    {k l : Fin d → ℤ} (hkl : k ≠ l) :
    Disjoint (Box.Ioo (boxGrid L hL k)) (Box.Ioo (boxGrid L hL l)) :=
  (disjoint_boxGrid hL hkl).mono
    (boxGrid L hL k).Ioo_subset_coe (boxGrid L hL l).Ioo_subset_coe

/-- Every grid box has the prescribed common coordinate width. -/
theorem upper_sub_lower_boxGrid {d : ℕ} (L : ℝ) (hL : 0 < L)
    (k : Fin d → ℤ) (i : Fin d) :
    (boxGrid L hL k).upper i - (boxGrid L hL k).lower i = L := by
  simp only [boxGrid_upper, boxGrid_lower]
  ring

/-- The coordinate center of a grid box. -/
theorem boxCenter_boxGrid_apply {d : ℕ} (L : ℝ) (hL : 0 < L)
    (k : Fin d → ℤ) (i : Fin d) :
    boxCenter (boxGrid L hL k) i = L * ((k i : ℝ) + 1 / 2) := by
  simp only [boxCenter, boxGrid_lower, boxGrid_upper]
  ring

/-- Every grid box has exact real volume `L ^ d`. -/
theorem volume_boxGrid_toReal {d : ℕ} (L : ℝ) (hL : 0 < L)
    (k : Fin d → ℤ) :
    (MeasureTheory.volume (boxGrid L hL k : Set (Vec d))).toReal = L ^ d :=
  volume_box_toReal_eq_pow_of_commonWidth (boxGrid L hL k) L
    (upper_sub_lower_boxGrid L hL k)

end PDE
