module

public import PDEFoundation.Geometry.AxisBox

/-!
# Dyadic square shells in dimension two

The dyadic shell between the closed square of half-side `r` and the open
square of half-side `2 * r` is covered exactly by four overlapping open
rectangles. Each rectangle is a bounded open convex domain, so the common
convex-domain Poincaré theorem can be applied locally. The three displayed
corner overlaps form the connected graph `top — left — bottom` and
`top — right` used to compare the four local means.
-/

@[expose] public section

namespace PDE

/-- The region between the closed square of half-side `r` and the open square
of half-side `2 * r`. -/
def dyadicSquareShell (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  centeredAxisCube x₀ (2 * r) \ closedCenteredAxisCube x₀ r

def dyadicSquareShellTop (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - 2 * r, x₀ 1 + r]
    ![x₀ 0 + 2 * r, x₀ 1 + 2 * r]

def dyadicSquareShellBottom (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - 2 * r, x₀ 1 - 2 * r]
    ![x₀ 0 + 2 * r, x₀ 1 - r]

def dyadicSquareShellLeft (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - 2 * r, x₀ 1 - 2 * r]
    ![x₀ 0 - r, x₀ 1 + 2 * r]

def dyadicSquareShellRight (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 + r, x₀ 1 - 2 * r]
    ![x₀ 0 + 2 * r, x₀ 1 + 2 * r]

def dyadicSquareShellStrips (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  (dyadicSquareShellTop x₀ r ∪ dyadicSquareShellBottom x₀ r) ∪
    (dyadicSquareShellLeft x₀ r ∪ dyadicSquareShellRight x₀ r)

def dyadicSquareShellTopLeftOverlap (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - 2 * r, x₀ 1 + r]
    ![x₀ 0 - r, x₀ 1 + 2 * r]

def dyadicSquareShellTopRightOverlap (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 + r, x₀ 1 + r]
    ![x₀ 0 + 2 * r, x₀ 1 + 2 * r]

def dyadicSquareShellBottomLeftOverlap (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  axisBox ![x₀ 0 - 2 * r, x₀ 1 - 2 * r]
    ![x₀ 0 - r, x₀ 1 - r]

theorem isOpen_dyadicSquareShell (x₀ : Vec 2) (r : ℝ) :
    IsOpen (dyadicSquareShell x₀ r) :=
  (isOpen_centeredAxisCube x₀ (2 * r)).sdiff
    (isClosed_closedCenteredAxisCube x₀ r)

/-- A positive-radius closed inner square lies strictly inside the open
square with twice the half-side. -/
theorem closedCenteredAxisCube_subset_centeredAxisCube_two
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    closedCenteredAxisCube x₀ r ⊆
      centeredAxisCube x₀ (2 * r) := by
  intro x hx i _
  have hxi := hx i (Set.mem_univ i)
  change x₀ i - r ≤ x i ∧ x i ≤ x₀ i + r at hxi
  change x₀ i - 2 * r < x i ∧ x i < x₀ i + 2 * r
  constructor <;> linarith [hxi.1, hxi.2]

theorem dyadicSquareShell_subset_strips (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShell x₀ r ⊆ dyadicSquareShellStrips x₀ r := by
  intro x hx
  have hOuter := hx.1
  have h0 : x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r := by
    simpa only [centeredAxisCube, axisBox, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo] using hOuter 0 (Set.mem_univ 0)
  have h1 : x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r := by
    simpa only [centeredAxisCube, axisBox, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioo] using hOuter 1 (Set.mem_univ 1)
  by_cases h0left : x 0 < x₀ 0 - r
  · refine Or.inr (Or.inl ?_)
    intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 - r
      exact ⟨h0.1, h0left⟩
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact h1
  by_cases h0right : x₀ 0 + r < x 0
  · refine Or.inr (Or.inr ?_)
    intro i _
    fin_cases i
    · change x₀ 0 + r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact ⟨h0right, h0.2⟩
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact h1
  by_cases h1bottom : x 1 < x₀ 1 - r
  · refine Or.inl (Or.inr ?_)
    intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact h0
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 - r
      exact ⟨h1.1, h1bottom⟩
  by_cases h1top : x₀ 1 + r < x 1
  · refine Or.inl (Or.inl ?_)
    intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact h0
    · change x₀ 1 + r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact ⟨h1top, h1.2⟩
  exfalso
  apply hx.2
  intro i _
  fin_cases i
  · change x₀ 0 - r ≤ x 0 ∧ x 0 ≤ x₀ 0 + r
    exact ⟨le_of_not_gt h0left, le_of_not_gt h0right⟩
  · change x₀ 1 - r ≤ x 1 ∧ x 1 ≤ x₀ 1 + r
    exact ⟨le_of_not_gt h1bottom, le_of_not_gt h1top⟩

theorem dyadicSquareShellTop_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellTop x₀ r ⊆ dyadicSquareShell x₀ r := by
  intro x hx
  have hx0 : x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r := by
    simpa only [dyadicSquareShellTop, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 + r < x 1 ∧ x 1 < x₀ 1 + 2 * r := by
    simpa only [dyadicSquareShellTop, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · exact hx0
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact ⟨by linarith [hx1.1], hx1.2⟩
  · intro hInner
    have hInner1 := hInner 1 (Set.mem_univ 1)
    change x₀ 1 - r ≤ x 1 ∧ x 1 ≤ x₀ 1 + r at hInner1
    exact (not_le_of_gt hx1.1) hInner1.2

theorem dyadicSquareShellBottom_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellBottom x₀ r ⊆ dyadicSquareShell x₀ r := by
  intro x hx
  have hx0 : x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r := by
    simpa only [dyadicSquareShellBottom, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 - r := by
    simpa only [dyadicSquareShellBottom, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · exact hx0
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact ⟨hx1.1, by linarith [hx1.2]⟩
  · intro hInner
    have hInner1 := hInner 1 (Set.mem_univ 1)
    change x₀ 1 - r ≤ x 1 ∧ x 1 ≤ x₀ 1 + r at hInner1
    exact (not_le_of_gt hx1.2) hInner1.1

theorem dyadicSquareShellLeft_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellLeft x₀ r ⊆ dyadicSquareShell x₀ r := by
  intro x hx
  have hx0 : x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 - r := by
    simpa only [dyadicSquareShellLeft, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r := by
    simpa only [dyadicSquareShellLeft, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact ⟨hx0.1, by linarith [hx0.2]⟩
    · exact hx1
  · intro hInner
    have hInner0 := hInner 0 (Set.mem_univ 0)
    change x₀ 0 - r ≤ x 0 ∧ x 0 ≤ x₀ 0 + r at hInner0
    exact (not_le_of_gt hx0.2) hInner0.1

theorem dyadicSquareShellRight_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellRight x₀ r ⊆ dyadicSquareShell x₀ r := by
  intro x hx
  have hx0 : x₀ 0 + r < x 0 ∧ x 0 < x₀ 0 + 2 * r := by
    simpa only [dyadicSquareShellRight, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r := by
    simpa only [dyadicSquareShellRight, axisBox, Set.mem_pi, Set.mem_univ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact ⟨by linarith [hx0.1], hx0.2⟩
    · exact hx1
  · intro hInner
    have hInner0 := hInner 0 (Set.mem_univ 0)
    change x₀ 0 - r ≤ x 0 ∧ x 0 ≤ x₀ 0 + r at hInner0
    exact (not_le_of_gt hx0.1) hInner0.2

theorem dyadicSquareShellStrips_subset
  (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellStrips x₀ r ⊆ dyadicSquareShell x₀ r := by
  rintro x (hx | hx)
  · rcases hx with htop | hbottom
    · exact dyadicSquareShellTop_subset x₀ r htop
    · exact dyadicSquareShellBottom_subset x₀ r hbottom
  · rcases hx with hleft | hright
    · exact dyadicSquareShellLeft_subset x₀ r hleft
    · exact dyadicSquareShellRight_subset x₀ r hright

theorem dyadicSquareShell_eq_strips
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShell x₀ r = dyadicSquareShellStrips x₀ r :=
  Set.Subset.antisymm
    (dyadicSquareShell_subset_strips x₀ r)
    (dyadicSquareShellStrips_subset x₀ r)

theorem dyadicSquareShellTop_domain (x₀ : Vec 2) (r : ℝ) :
    IsOpenBoundedConvexDomain (dyadicSquareShellTop x₀ r) :=
  isOpenBoundedConvexDomain_axisBox _ _

theorem dyadicSquareShellBottom_domain (x₀ : Vec 2) (r : ℝ) :
    IsOpenBoundedConvexDomain (dyadicSquareShellBottom x₀ r) :=
  isOpenBoundedConvexDomain_axisBox _ _

theorem dyadicSquareShellLeft_domain (x₀ : Vec 2) (r : ℝ) :
    IsOpenBoundedConvexDomain (dyadicSquareShellLeft x₀ r) :=
  isOpenBoundedConvexDomain_axisBox _ _

theorem dyadicSquareShellRight_domain (x₀ : Vec 2) (r : ℝ) :
    IsOpenBoundedConvexDomain (dyadicSquareShellRight x₀ r) :=
  isOpenBoundedConvexDomain_axisBox _ _

theorem dyadicSquareShellTop_nonempty (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    (dyadicSquareShellTop x₀ r).Nonempty := by
  apply axisBox_nonempty
  intro i
  fin_cases i
  · change x₀ 0 - 2 * r < x₀ 0 + 2 * r
    linarith
  · change x₀ 1 + r < x₀ 1 + 2 * r
    linarith

theorem dyadicSquareShellBottom_nonempty (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    (dyadicSquareShellBottom x₀ r).Nonempty := by
  apply axisBox_nonempty
  intro i
  fin_cases i
  · change x₀ 0 - 2 * r < x₀ 0 + 2 * r
    linarith
  · change x₀ 1 - 2 * r < x₀ 1 - r
    linarith

theorem dyadicSquareShellLeft_nonempty (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    (dyadicSquareShellLeft x₀ r).Nonempty := by
  apply axisBox_nonempty
  intro i
  fin_cases i
  · change x₀ 0 - 2 * r < x₀ 0 - r
    linarith
  · change x₀ 1 - 2 * r < x₀ 1 + 2 * r
    linarith

theorem dyadicSquareShellRight_nonempty (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    (dyadicSquareShellRight x₀ r).Nonempty := by
  apply axisBox_nonempty
  intro i
  fin_cases i
  · change x₀ 0 + r < x₀ 0 + 2 * r
    linarith
  · change x₀ 1 - 2 * r < x₀ 1 + 2 * r
    linarith

theorem dyadicSquareShellTop_diameter (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    HasEuclideanDiameterLE (dyadicSquareShellTop x₀ r)
      (Real.sqrt 2 * (4 * r)) := by
  apply hasEuclideanDiameterLE_axisBox_of_side_le _ _ (by positivity)
  intro i
  fin_cases i
  · change (x₀ 0 + 2 * r) - (x₀ 0 - 2 * r) ≤ 4 * r
    ring_nf
    rfl
  · change (x₀ 1 + 2 * r) - (x₀ 1 + r) ≤ 4 * r
    linarith

theorem dyadicSquareShellBottom_diameter (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    HasEuclideanDiameterLE (dyadicSquareShellBottom x₀ r)
      (Real.sqrt 2 * (4 * r)) := by
  apply hasEuclideanDiameterLE_axisBox_of_side_le _ _ (by positivity)
  intro i
  fin_cases i
  · change (x₀ 0 + 2 * r) - (x₀ 0 - 2 * r) ≤ 4 * r
    ring_nf
    rfl
  · change (x₀ 1 - r) - (x₀ 1 - 2 * r) ≤ 4 * r
    linarith

theorem dyadicSquareShellLeft_diameter (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    HasEuclideanDiameterLE (dyadicSquareShellLeft x₀ r)
      (Real.sqrt 2 * (4 * r)) := by
  apply hasEuclideanDiameterLE_axisBox_of_side_le _ _ (by positivity)
  intro i
  fin_cases i
  · change (x₀ 0 - r) - (x₀ 0 - 2 * r) ≤ 4 * r
    linarith
  · change (x₀ 1 + 2 * r) - (x₀ 1 - 2 * r) ≤ 4 * r
    ring_nf
    rfl

theorem dyadicSquareShellRight_diameter (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    HasEuclideanDiameterLE (dyadicSquareShellRight x₀ r)
      (Real.sqrt 2 * (4 * r)) := by
  apply hasEuclideanDiameterLE_axisBox_of_side_le _ _ (by positivity)
  intro i
  fin_cases i
  · change (x₀ 0 + 2 * r) - (x₀ 0 + r) ≤ 4 * r
    linarith
  · change (x₀ 1 + 2 * r) - (x₀ 1 - 2 * r) ≤ 4 * r
    ring_nf
    rfl

theorem dyadicSquareShellTopLeftOverlap_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellTopLeftOverlap x₀ r ⊆
      dyadicSquareShellTop x₀ r ∩ dyadicSquareShellLeft x₀ r := by
  intro x hx
  have hx0 : x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 - r := by
    simpa only [dyadicSquareShellTopLeftOverlap, axisBox, Set.mem_pi,
      Set.mem_univ, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 + r < x 1 ∧ x 1 < x₀ 1 + 2 * r := by
    simpa only [dyadicSquareShellTopLeftOverlap, axisBox, Set.mem_pi,
      Set.mem_univ, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact ⟨hx0.1, by linarith [hx0.2]⟩
    · exact hx1
  · intro i _
    fin_cases i
    · exact hx0
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact ⟨by linarith [hx1.1], hx1.2⟩

theorem dyadicSquareShellTopRightOverlap_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellTopRightOverlap x₀ r ⊆
      dyadicSquareShellTop x₀ r ∩ dyadicSquareShellRight x₀ r := by
  intro x hx
  have hx0 : x₀ 0 + r < x 0 ∧ x 0 < x₀ 0 + 2 * r := by
    simpa only [dyadicSquareShellTopRightOverlap, axisBox, Set.mem_pi,
      Set.mem_univ, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 + r < x 1 ∧ x 1 < x₀ 1 + 2 * r := by
    simpa only [dyadicSquareShellTopRightOverlap, axisBox, Set.mem_pi,
      Set.mem_univ, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact ⟨by linarith [hx0.1], hx0.2⟩
    · exact hx1
  · intro i _
    fin_cases i
    · exact hx0
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact ⟨by linarith [hx1.1], hx1.2⟩

theorem dyadicSquareShellBottomLeftOverlap_subset
    (x₀ : Vec 2) (r : ℝ) :
    dyadicSquareShellBottomLeftOverlap x₀ r ⊆
      dyadicSquareShellBottom x₀ r ∩ dyadicSquareShellLeft x₀ r := by
  intro x hx
  have hx0 : x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 - r := by
    simpa only [dyadicSquareShellBottomLeftOverlap, axisBox, Set.mem_pi,
      Set.mem_univ, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 0 (Set.mem_univ 0)
  have hx1 : x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 - r := by
    simpa only [dyadicSquareShellBottomLeftOverlap, axisBox, Set.mem_pi,
      Set.mem_univ, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Ioo] using
      hx 1 (Set.mem_univ 1)
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      exact ⟨hx0.1, by linarith [hx0.2]⟩
    · exact hx1
  · intro i _
    fin_cases i
    · exact hx0
    · change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      exact ⟨hx1.1, by linarith [hx1.2]⟩

theorem measurableSet_dyadicSquareShell (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShell x₀ r) :=
  (isOpen_dyadicSquareShell x₀ r).measurableSet

theorem measurableSet_dyadicSquareShellTop (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellTop x₀ r) :=
  (dyadicSquareShellTop_domain x₀ r).isOpen.measurableSet

theorem measurableSet_dyadicSquareShellBottom (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellBottom x₀ r) :=
  (dyadicSquareShellBottom_domain x₀ r).isOpen.measurableSet

theorem measurableSet_dyadicSquareShellLeft (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellLeft x₀ r) :=
  (dyadicSquareShellLeft_domain x₀ r).isOpen.measurableSet

theorem measurableSet_dyadicSquareShellRight (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellRight x₀ r) :=
  (dyadicSquareShellRight_domain x₀ r).isOpen.measurableSet

theorem measurableSet_dyadicSquareShellTopLeftOverlap (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellTopLeftOverlap x₀ r) :=
  isOpen_axisBox _ _ |>.measurableSet

theorem measurableSet_dyadicSquareShellTopRightOverlap (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellTopRightOverlap x₀ r) :=
  isOpen_axisBox _ _ |>.measurableSet

theorem measurableSet_dyadicSquareShellBottomLeftOverlap (x₀ : Vec 2) (r : ℝ) :
    MeasurableSet (dyadicSquareShellBottomLeftOverlap x₀ r) :=
  isOpen_axisBox _ _ |>.measurableSet

end PDE
