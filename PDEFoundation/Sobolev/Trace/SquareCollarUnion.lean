module

public import PDEFoundation.Measure.L2CoverGluing
public import PDEFoundation.Measure.ShrinkingAxisBoxCollar
public import PDEFoundation.Sobolev.Cutoff.AxisBox
public import PDEFoundation.Sobolev.Trace.SquareCollar

/-!
# The four-collar cover of a square inset

Removing a closed `δ`-inset from an open centered square leaves a set covered
by its four literal open side collars.  This elementary geometry is kept
separate from the analytic one-dimensional estimates in `SquareCollar`, so
the cutoff-convergence argument can use one exact cover theorem and one
exact four-term integral estimate.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The left open collar of width `δ` in a centered square. -/
def centeredSquareLeftCollar (x₀ : Vec 2) (r δ : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - r, x₀ 1 - r] ![x₀ 0 - r + δ, x₀ 1 + r]

/-- The right open collar of width `δ` in a centered square. -/
def centeredSquareRightCollar (x₀ : Vec 2) (r δ : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 + r - δ, x₀ 1 - r] ![x₀ 0 + r, x₀ 1 + r]

/-- The bottom open collar of width `δ` in a centered square. -/
def centeredSquareBottomCollar (x₀ : Vec 2) (r δ : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - r, x₀ 1 - r] ![x₀ 0 + r, x₀ 1 - r + δ]

/-- The top open collar of width `δ` in a centered square. -/
def centeredSquareTopCollar (x₀ : Vec 2) (r δ : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - r, x₀ 1 + r - δ] ![x₀ 0 + r, x₀ 1 + r]

/-- The square collar is the overlapping union of its four literal side
collars, grouped for the four-set integral gluing lemma. -/
def centeredSquareCollar (x₀ : Vec 2) (r δ : ℝ) : Set (Vec 2) :=
  (centeredSquareLeftCollar x₀ r δ ∪ centeredSquareRightCollar x₀ r δ) ∪
    (centeredSquareBottomCollar x₀ r δ ∪ centeredSquareTopCollar x₀ r δ)

/-- The closed coordinatewise `δ`-inset is exactly the centered closed cube
whose half-side has decreased from `r` to `r - δ`. -/
theorem axisBoxInteriorInset_eq_closedCenteredAxisCube
    (x₀ : Vec 2) (r δ : ℝ) :
    axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
      (x₀ 1 - r) (x₀ 1 + r) δ =
      closedCenteredAxisCube x₀ (r - δ) := by
  ext x
  constructor
  · intro hx i _
    fin_cases i
    · have h := hx 0 (Set.mem_univ 0)
      change x₀ 0 - r + δ ≤ x 0 ∧ x 0 ≤ x₀ 0 + r - δ at h
      change x₀ 0 - (r - δ) ≤ x 0 ∧ x 0 ≤ x₀ 0 + (r - δ)
      constructor <;> linarith
    · have h := hx 1 (Set.mem_univ 1)
      change x₀ 1 - r + δ ≤ x 1 ∧ x 1 ≤ x₀ 1 + r - δ at h
      change x₀ 1 - (r - δ) ≤ x 1 ∧ x 1 ≤ x₀ 1 + (r - δ)
      constructor <;> linarith
  · intro hx i _
    fin_cases i
    · have h := hx 0 (Set.mem_univ 0)
      change x₀ 0 - (r - δ) ≤ x 0 ∧ x 0 ≤ x₀ 0 + (r - δ) at h
      change x₀ 0 - r + δ ≤ x 0 ∧ x 0 ≤ x₀ 0 + r - δ
      constructor <;> linarith
    · have h := hx 1 (Set.mem_univ 1)
      change x₀ 1 - (r - δ) ≤ x 1 ∧ x 1 ≤ x₀ 1 + (r - δ) at h
      change x₀ 1 - r + δ ≤ x 1 ∧ x 1 ≤ x₀ 1 + r - δ
      constructor <;> linarith

/-- The inset complement used by the cutoff construction is exactly the
literal shrinking boundary collar. -/
theorem centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar
    (x₀ : Vec 2) (r δ : ℝ) :
    centeredAxisCube x₀ r \
      axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
        (x₀ 1 - r) (x₀ 1 + r) δ =
      centeredAxisCubeBoundaryCollar x₀ r δ := by
  rw [axisBoxInteriorInset_eq_closedCenteredAxisCube]
  rfl

/-- The complement in the open square of its closed `δ`-inset is covered by
the four open side collars.  The statement is valid also at `δ = 0`, where
the left-hand set is empty. -/
theorem centeredAxisCube_diff_axisBoxInteriorInset_subset_centeredSquareCollar
    (x₀ : Vec 2) (r δ : ℝ) :
    centeredAxisCube x₀ r \
      axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
        (x₀ 1 - r) (x₀ 1 + r) δ ⊆
      centeredSquareCollar x₀ r δ := by
  intro x hx
  have hxOuter := hx.1
  have hx0 : x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r := by
    simpa only [centeredAxisCube, axisBox, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo] using hxOuter 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r := by
    simpa only [centeredAxisCube, axisBox, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo] using hxOuter 1 (Set.mem_univ 1)
  by_cases hxleft : x 0 < x₀ 0 - r + δ
  · refine Or.inl (Or.inl ?_)
    intro i _
    fin_cases i
    · change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 - r + δ
      exact ⟨hx0.1, hxleft⟩
    · change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r
      exact hx1
  by_cases hxright : x₀ 0 + r - δ < x 0
  · refine Or.inl (Or.inr ?_)
    intro i _
    fin_cases i
    · change x₀ 0 + r - δ < x 0 ∧ x 0 < x₀ 0 + r
      exact ⟨hxright, hx0.2⟩
    · change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r
      exact hx1
  by_cases hxbottom : x 1 < x₀ 1 - r + δ
  · refine Or.inr (Or.inl ?_)
    intro i _
    fin_cases i
    · change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r
      exact hx0
    · change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 - r + δ
      exact ⟨hx1.1, hxbottom⟩
  by_cases hxtop : x₀ 1 + r - δ < x 1
  · refine Or.inr (Or.inr ?_)
    intro i _
    fin_cases i
    · change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r
      exact hx0
    · change x₀ 1 + r - δ < x 1 ∧ x 1 < x₀ 1 + r
      exact ⟨hxtop, hx1.2⟩
  exfalso
  apply hx.2
  intro i _
  fin_cases i
  · change x₀ 0 - r + δ ≤ x 0 ∧ x 0 ≤ x₀ 0 + r - δ
    exact ⟨le_of_not_gt hxleft, le_of_not_gt hxright⟩
  · change x₀ 1 - r + δ ≤ x 1 ∧ x 1 ≤ x₀ 1 + r - δ
    exact ⟨le_of_not_gt hxbottom, le_of_not_gt hxtop⟩

private theorem centeredSquareLeftCollar_subset_centeredAxisCube
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareLeftCollar x₀ r δ ⊆ centeredAxisCube x₀ r := by
  intro x hx i _
  fin_cases i
  · have h := hx 0 (Set.mem_univ 0)
    change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 - r + δ at h
    change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r
    constructor <;> linarith [hδ.2]
  · have h := hx 1 (Set.mem_univ 1)
    change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r at h
    exact h

private theorem centeredSquareRightCollar_subset_centeredAxisCube
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareRightCollar x₀ r δ ⊆ centeredAxisCube x₀ r := by
  intro x hx i _
  fin_cases i
  · have h := hx 0 (Set.mem_univ 0)
    change x₀ 0 + r - δ < x 0 ∧ x 0 < x₀ 0 + r at h
    change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r
    constructor <;> linarith [hδ.2]
  · have h := hx 1 (Set.mem_univ 1)
    change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r at h
    exact h

private theorem centeredSquareBottomCollar_subset_centeredAxisCube
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareBottomCollar x₀ r δ ⊆ centeredAxisCube x₀ r := by
  intro x hx i _
  fin_cases i
  · have h := hx 0 (Set.mem_univ 0)
    change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r at h
    exact h
  · have h := hx 1 (Set.mem_univ 1)
    change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 - r + δ at h
    change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r
    constructor <;> linarith [hδ.2]

private theorem centeredSquareTopCollar_subset_centeredAxisCube
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareTopCollar x₀ r δ ⊆ centeredAxisCube x₀ r := by
  intro x hx i _
  fin_cases i
  · have h := hx 0 (Set.mem_univ 0)
    change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 + r at h
    exact h
  · have h := hx 1 (Set.mem_univ 1)
    change x₀ 1 + r - δ < x 1 ∧ x 1 < x₀ 1 + r at h
    change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 + r
    constructor <;> linarith [hδ.2]

/-- For an admissible width, each literal side collar lies outside the closed
inset, so the four-collar union is contained in the inset complement. -/
theorem centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareCollar x₀ r δ ⊆
      centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) δ := by
  intro x hx
  rcases hx with (hx | hx) | (hx | hx)
  · refine ⟨centeredSquareLeftCollar_subset_centeredAxisCube hδ hx, ?_⟩
    intro hinset
    have hinner := hinset 0 (Set.mem_univ 0)
    have hcollar := hx 0 (Set.mem_univ 0)
    change x₀ 0 - r + δ ≤ x 0 ∧ x 0 ≤ x₀ 0 + r - δ at hinner
    change x₀ 0 - r < x 0 ∧ x 0 < x₀ 0 - r + δ at hcollar
    exact (not_lt_of_ge hinner.1) hcollar.2
  · refine ⟨centeredSquareRightCollar_subset_centeredAxisCube hδ hx, ?_⟩
    intro hinset
    have hinner := hinset 0 (Set.mem_univ 0)
    have hcollar := hx 0 (Set.mem_univ 0)
    change x₀ 0 - r + δ ≤ x 0 ∧ x 0 ≤ x₀ 0 + r - δ at hinner
    change x₀ 0 + r - δ < x 0 ∧ x 0 < x₀ 0 + r at hcollar
    exact (not_lt_of_ge hinner.2) hcollar.1
  · refine ⟨centeredSquareBottomCollar_subset_centeredAxisCube hδ hx, ?_⟩
    intro hinset
    have hinner := hinset 1 (Set.mem_univ 1)
    have hcollar := hx 1 (Set.mem_univ 1)
    change x₀ 1 - r + δ ≤ x 1 ∧ x 1 ≤ x₀ 1 + r - δ at hinner
    change x₀ 1 - r < x 1 ∧ x 1 < x₀ 1 - r + δ at hcollar
    exact (not_lt_of_ge hinner.1) hcollar.2
  · refine ⟨centeredSquareTopCollar_subset_centeredAxisCube hδ hx, ?_⟩
    intro hinset
    have hinner := hinset 1 (Set.mem_univ 1)
    have hcollar := hx 1 (Set.mem_univ 1)
    change x₀ 1 - r + δ ≤ x 1 ∧ x 1 ≤ x₀ 1 + r - δ at hinner
    change x₀ 1 + r - δ < x 1 ∧ x 1 < x₀ 1 + r at hcollar
    exact (not_lt_of_ge hinner.2) hcollar.1

/-- At every admissible width, the overlapping four-side union is exactly the
part of the open square outside the closed inset. -/
theorem centeredSquareCollar_eq_centeredAxisCube_diff_axisBoxInteriorInset
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareCollar x₀ r δ =
      centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) δ :=
  Set.Subset.antisymm
    (centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ)
    (centeredAxisCube_diff_axisBoxInteriorInset_subset_centeredSquareCollar
      x₀ r δ)

theorem centeredSquareLeftCollar_subset_centeredAxisCubeBoundaryCollar
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareLeftCollar x₀ r δ ⊆
      centeredAxisCubeBoundaryCollar x₀ r δ := by
  rw [← centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar]
  intro x hx
  exact
    centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inl (Or.inl hx))

theorem centeredSquareRightCollar_subset_centeredAxisCubeBoundaryCollar
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareRightCollar x₀ r δ ⊆
      centeredAxisCubeBoundaryCollar x₀ r δ := by
  rw [← centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar]
  intro x hx
  exact
    centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inl (Or.inr hx))

theorem centeredSquareBottomCollar_subset_centeredAxisCubeBoundaryCollar
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareBottomCollar x₀ r δ ⊆
      centeredAxisCubeBoundaryCollar x₀ r δ := by
  rw [← centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar]
  intro x hx
  exact
    centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inr (Or.inl hx))

theorem centeredSquareTopCollar_subset_centeredAxisCubeBoundaryCollar
    {x₀ : Vec 2} {r δ : ℝ} (hδ : δ ∈ Icc 0 (2 * r)) :
    centeredSquareTopCollar x₀ r δ ⊆
      centeredAxisCubeBoundaryCollar x₀ r δ := by
  rw [← centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar]
  intro x hx
  exact
    centeredSquareCollar_subset_centeredAxisCube_diff_axisBoxInteriorInset hδ
      (Or.inr (Or.inr hx))

private theorem integrableOn_sq_max_sub_const_of_axisBox_subset
    {u : Vec 2 → ℝ} {k : ℝ} {S Q : Set (Vec 2)}
    (hSQ : S ⊆ Q) (hu : MemL2On Q u)
    (hfinite : volume S ≠ ⊤) :
    IntegrableOn (fun x => (max (u x - k) 0) ^ 2) S volume := by
  let : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfinite.lt_top⟩
  have huS : MemL2On S u := memLpOn_mono hSQ hu
  have hshift : MemLp (fun x => u x - k) 2 (volume.restrict S) := by
    simpa only [Pi.sub_apply] using! huS.sub (memLp_const k)
  have htrunc : MemL2On S (fun x => max (u x - k) 0) := by
    simpa only using hshift.pos_part
  simpa only [IntegrableOn] using htrunc.integrable_sq

/-- Combining the four one-dimensional collar bounds costs no geometric
constant: the inset-complement energy is bounded by `δ²` times the displayed
sum of the four literal normal-coordinate energies. -/
theorem SquareNormalTraceCertificate.setIntegral_sq_max_sub_const_le_square_collar
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r δ k : ℝ}
    (C : SquareNormalTraceCertificate F u g x₀ r)
    (hδ : δ ∈ Icc 0 (2 * r))
    (hleft : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      C.traceProvenance.trace.left t ≤ k)
    (hright : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      C.traceProvenance.trace.right t ≤ k)
    (hbottom : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      C.traceProvenance.trace.bottom s ≤ k)
    (htop : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      C.traceProvenance.trace.top s ≤ k) :
    ∫ x in centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) δ,
        (max (u x - k) 0) ^ 2 ∂volume ≤
      δ ^ 2 *
        ((∫ x in centeredSquareLeftCollar x₀ r δ, (g x 0) ^ 2 ∂volume) +
          (∫ x in centeredSquareRightCollar x₀ r δ, (g x 0) ^ 2 ∂volume) +
          (∫ x in centeredSquareBottomCollar x₀ r δ, (g x 1) ^ 2 ∂volume) +
          ∫ x in centeredSquareTopCollar x₀ r δ, (g x 1) ^ 2 ∂volume) := by
  let L := centeredSquareLeftCollar x₀ r δ
  let R := centeredSquareRightCollar x₀ r δ
  let B := centeredSquareBottomCollar x₀ r δ
  let T := centeredSquareTopCollar x₀ r δ
  have hL : L ⊆ centeredAxisCube x₀ r :=
    centeredSquareLeftCollar_subset_centeredAxisCube hδ
  have hR : R ⊆ centeredAxisCube x₀ r :=
    centeredSquareRightCollar_subset_centeredAxisCube hδ
  have hB : B ⊆ centeredAxisCube x₀ r :=
    centeredSquareBottomCollar_subset_centeredAxisCube hδ
  have hT : T ⊆ centeredAxisCube x₀ r :=
    centeredSquareTopCollar_subset_centeredAxisCube hδ
  have hcentered : centeredAxisCube x₀ r =
      axisBox ![x₀ 0 - r, x₀ 1 - r] ![x₀ 0 + r, x₀ 1 + r] := by
    unfold centeredAxisCube
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hLBox : L ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hL
  have hRBox : R ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hR
  have hBBox : B ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hB
  have hTBox : T ⊆ axisBox ![x₀ 0 - r, x₀ 1 - r]
      ![x₀ 0 + r, x₀ 1 + r] := by
    simpa only [hcentered] using hT
  have hLInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) L volume := by
    apply integrableOn_sq_max_sub_const_of_axisBox_subset hLBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hRInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) R volume := by
    apply integrableOn_sq_max_sub_const_of_axisBox_subset hRBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hBInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) B volume := by
    apply integrableOn_sq_max_sub_const_of_axisBox_subset hBBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hTInt : IntegrableOn (fun x => (max (u x - k) 0) ^ 2) T volume := by
    apply integrableOn_sq_max_sub_const_of_axisBox_subset hTBox
      C.normalSliceData.valueMemL2
    exact volume_axisBox_ne_top _ _
  have hcover : centeredAxisCube x₀ r \
      axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
        (x₀ 1 - r) (x₀ 1 + r) δ ⊆ (L ∪ R) ∪ (B ∪ T) :=
    centeredAxisCube_diff_axisBoxInteriorInset_subset_centeredSquareCollar x₀ r δ
  have hleft' := C.setIntegral_sq_max_sub_const_le_left_collar hδ hleft
  have hright' := C.setIntegral_sq_max_sub_const_le_right_collar hδ hright
  have hbottom' := C.setIntegral_sq_max_sub_const_le_bottom_collar hδ hbottom
  have htop' := C.setIntegral_sq_max_sub_const_le_top_collar hδ htop
  have hleftL : (∫ x in L, (max (u x - k) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in L, (g x 0) ^ 2 ∂volume := by
    simpa only [L, centeredSquareLeftCollar] using hleft'
  have hrightR : (∫ x in R, (max (u x - k) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in R, (g x 0) ^ 2 ∂volume := by
    simpa only [R, centeredSquareRightCollar] using hright'
  have hbottomB : (∫ x in B, (max (u x - k) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in B, (g x 1) ^ 2 ∂volume := by
    simpa only [B, centeredSquareBottomCollar] using hbottom'
  have htopT : (∫ x in T, (max (u x - k) 0) ^ 2 ∂volume) ≤
      δ ^ 2 * ∫ x in T, (g x 1) ^ 2 ∂volume := by
    simpa only [T, centeredSquareTopCollar] using htop'
  calc
    ∫ x in centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) δ,
        (max (u x - k) 0) ^ 2 ∂volume ≤
        (∫ x in L, (max (u x - k) 0) ^ 2 ∂volume) +
          (∫ x in R, (max (u x - k) 0) ^ 2 ∂volume) +
          (∫ x in B, (max (u x - k) 0) ^ 2 ∂volume) +
          ∫ x in T, (max (u x - k) 0) ^ 2 ∂volume :=
      setIntegral_le_sum_four_of_subset_union hcover hLInt hRInt hBInt hTInt
        (fun x => sq_nonneg _)
    _ ≤ δ ^ 2 * (∫ x in L, (g x 0) ^ 2 ∂volume) +
          δ ^ 2 * (∫ x in R, (g x 0) ^ 2 ∂volume) +
          δ ^ 2 * (∫ x in B, (g x 1) ^ 2 ∂volume) +
          δ ^ 2 * ∫ x in T, (g x 1) ^ 2 ∂volume := by
      gcongr
    _ = δ ^ 2 *
        ((∫ x in L, (g x 0) ^ 2 ∂volume) +
          (∫ x in R, (g x 0) ^ 2 ∂volume) +
          (∫ x in B, (g x 1) ^ 2 ∂volume) +
          ∫ x in T, (g x 1) ^ 2 ∂volume) := by ring

end

end PDE
