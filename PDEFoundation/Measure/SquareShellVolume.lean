module

public import PDEFoundation.Geometry.SquareShell
public import PDEFoundation.Measure.AxisBoxVolume
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Volumes in the dyadic square-shell cover

In dimension two, every strip in the standard cover of
`Q_{2r}(x₀) \ closed Q_r(x₀)` has area `4 * r²`, while each of the three
corner overlaps in the connected gluing graph has area `r²`.
-/

@[expose] public section

namespace PDE

open MeasureTheory

theorem volume_dyadicSquareShellTop_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellTop x₀ r)).toReal = 4 * r ^ 2 := by
  rw [dyadicSquareShellTop, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 - 2 * r ≤ x₀ 0 + 2 * r
      linarith
    · change x₀ 1 + r ≤ x₀ 1 + 2 * r
      linarith

theorem volume_dyadicSquareShellBottom_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellBottom x₀ r)).toReal = 4 * r ^ 2 := by
  rw [dyadicSquareShellBottom, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 - 2 * r ≤ x₀ 0 + 2 * r
      linarith
    · change x₀ 1 - 2 * r ≤ x₀ 1 - r
      linarith

theorem volume_dyadicSquareShellLeft_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellLeft x₀ r)).toReal = 4 * r ^ 2 := by
  rw [dyadicSquareShellLeft, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 - 2 * r ≤ x₀ 0 - r
      linarith
    · change x₀ 1 - 2 * r ≤ x₀ 1 + 2 * r
      linarith

theorem volume_dyadicSquareShellRight_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellRight x₀ r)).toReal = 4 * r ^ 2 := by
  rw [dyadicSquareShellRight, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 + r ≤ x₀ 0 + 2 * r
      linarith
    · change x₀ 1 - 2 * r ≤ x₀ 1 + 2 * r
      linarith

theorem volume_dyadicSquareShellTopLeftOverlap_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellTopLeftOverlap x₀ r)).toReal = r ^ 2 := by
  rw [dyadicSquareShellTopLeftOverlap, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 - 2 * r ≤ x₀ 0 - r
      linarith
    · change x₀ 1 + r ≤ x₀ 1 + 2 * r
      linarith

theorem volume_dyadicSquareShellTopRightOverlap_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellTopRightOverlap x₀ r)).toReal = r ^ 2 := by
  rw [dyadicSquareShellTopRightOverlap, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 + r ≤ x₀ 0 + 2 * r
      linarith
    · change x₀ 1 + r ≤ x₀ 1 + 2 * r
      linarith

theorem volume_dyadicSquareShellBottomLeftOverlap_toReal
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    (volume (dyadicSquareShellBottomLeftOverlap x₀ r)).toReal = r ^ 2 := by
  rw [dyadicSquareShellBottomLeftOverlap, volume_axisBox_toReal]
  · norm_num [Fin.prod_univ_two]
    ring
  · intro i
    fin_cases i
    · change x₀ 0 - 2 * r ≤ x₀ 0 - r
      linarith
    · change x₀ 1 - 2 * r ≤ x₀ 1 - r
      linarith

theorem volume_dyadicSquareShellTopLeftOverlap_pos
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    0 < volume (dyadicSquareShellTopLeftOverlap x₀ r) := by
  apply volume_axisBox_pos
  intro i
  fin_cases i
  · change x₀ 0 - 2 * r < x₀ 0 - r
    linarith
  · change x₀ 1 + r < x₀ 1 + 2 * r
    linarith

theorem volume_dyadicSquareShellTopRightOverlap_pos
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    0 < volume (dyadicSquareShellTopRightOverlap x₀ r) := by
  apply volume_axisBox_pos
  intro i
  fin_cases i
  · change x₀ 0 + r < x₀ 0 + 2 * r
    linarith
  · change x₀ 1 + r < x₀ 1 + 2 * r
    linarith

theorem volume_dyadicSquareShellBottomLeftOverlap_pos
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    0 < volume (dyadicSquareShellBottomLeftOverlap x₀ r) := by
  apply volume_axisBox_pos
  intro i
  fin_cases i
  · change x₀ 0 - 2 * r < x₀ 0 - r
    linarith
  · change x₀ 1 - 2 * r < x₀ 1 - r
    linarith

/-- The top-left strip intersection has real volume at least `r²`. The
explicit overlap box is sufficient; no exact intersection identity is
needed by the gluing argument. -/
theorem sq_le_volumeReal_dyadicSquareShellTop_inter_left
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 ≤
      volume.real
        (dyadicSquareShellTop x₀ r ∩ dyadicSquareShellLeft x₀ r) := by
  calc
    r ^ 2 =
        volume.real (dyadicSquareShellTopLeftOverlap x₀ r) := by
      symm
      exact volume_dyadicSquareShellTopLeftOverlap_toReal x₀ hr
    _ ≤ volume.real
        (dyadicSquareShellTop x₀ r ∩ dyadicSquareShellLeft x₀ r) := by
      apply measureReal_mono
      · exact dyadicSquareShellTopLeftOverlap_subset x₀ r
      · exact measure_ne_top_of_subset Set.inter_subset_left
          (volume_axisBox_ne_top _ _)

/-- The top-right strip intersection has real volume at least `r²`. -/
theorem sq_le_volumeReal_dyadicSquareShellTop_inter_right
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 ≤
      volume.real
        (dyadicSquareShellTop x₀ r ∩ dyadicSquareShellRight x₀ r) := by
  calc
    r ^ 2 =
        volume.real (dyadicSquareShellTopRightOverlap x₀ r) := by
      symm
      exact volume_dyadicSquareShellTopRightOverlap_toReal x₀ hr
    _ ≤ volume.real
        (dyadicSquareShellTop x₀ r ∩ dyadicSquareShellRight x₀ r) := by
      apply measureReal_mono
      · exact dyadicSquareShellTopRightOverlap_subset x₀ r
      · exact measure_ne_top_of_subset Set.inter_subset_left
          (volume_axisBox_ne_top _ _)

/-- The left-bottom strip intersection has real volume at least `r²`. -/
theorem sq_le_volumeReal_dyadicSquareShellLeft_inter_bottom
    (x₀ : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 ≤
      volume.real
        (dyadicSquareShellLeft x₀ r ∩ dyadicSquareShellBottom x₀ r) := by
  calc
    r ^ 2 =
        volume.real (dyadicSquareShellBottomLeftOverlap x₀ r) := by
      symm
      exact volume_dyadicSquareShellBottomLeftOverlap_toReal x₀ hr
    _ ≤ volume.real
        (dyadicSquareShellLeft x₀ r ∩ dyadicSquareShellBottom x₀ r) := by
      apply measureReal_mono
      · intro x hx
        have h :=
          dyadicSquareShellBottomLeftOverlap_subset x₀ r hx
        exact ⟨h.2, h.1⟩
      · exact measure_ne_top_of_subset Set.inter_subset_left
          (volume_axisBox_ne_top _ _)

end PDE
