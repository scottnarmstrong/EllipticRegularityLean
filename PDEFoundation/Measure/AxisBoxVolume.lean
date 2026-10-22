module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open scoped ENNReal

/-!
# Volume of axis-aligned boxes

The volume is the product of the coordinate side lengths. Both the extended
volume identity and the real-valued form used by energy estimates are
exported.
-/

namespace PDE

open MeasureTheory

theorem volume_axisBox {d : ℕ} (a b : Vec d) :
    volume (axisBox a b) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [axisBox, Real.volume_pi_Ioo]

theorem volume_axisBox_ne_top {d : ℕ} (a b : Vec d) :
    volume (axisBox a b) ≠ ∞ :=
  (isBoundedDomain_axisBox a b).volume_lt_top.ne

theorem volume_axisBox_toReal {d : ℕ}
    (a b : Vec d) (hab : a ≤ b) :
    (volume (axisBox a b)).toReal =
      ∏ i, (b i - a i) := by
  rw [axisBox, Real.volume_pi_Ioo_toReal hab]

theorem volume_axisBox_pos {d : ℕ}
    (a b : Vec d) (hab : ∀ i, a i < b i) :
    0 < volume (axisBox a b) :=
  (isOpenBoundedConvexDomain_axisBox a b).volume_pos
    (axisBox_nonempty a b hab)

theorem volume_axisBox_toReal_pos {d : ℕ}
    (a b : Vec d) (hab : ∀ i, a i < b i) :
    0 < (volume (axisBox a b)).toReal :=
  ENNReal.toReal_pos (volume_axisBox_pos a b hab).ne'
    (volume_axisBox_ne_top a b)

/-- The exact real volume of an open centered cube of half-side `R`. -/
theorem volume_centeredAxisCube_toReal {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    (volume (centeredAxisCube x₀ R)).toReal = (2 * R) ^ d := by
  rw [centeredAxisCube, volume_axisBox_toReal]
  · simp_rw [show (x₀ _ + R) - (x₀ _ - R) = 2 * R by ring]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro i
    linarith

/-- The exact extended-real volume of an open centered cube of nonnegative
half-side `R`. -/
theorem volume_centeredAxisCube {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume (centeredAxisCube x₀ R) =
      ENNReal.ofReal ((2 * R) ^ d) := by
  rw [centeredAxisCube, volume_axisBox]
  simp_rw [show (x₀ _ + R) - (x₀ _ - R) = 2 * R by ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow]
  simp [hR]

/-- An open centered cube has finite volume at every scale. -/
theorem volume_centeredAxisCube_ne_top {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    volume (centeredAxisCube x₀ R) ≠ ∞ :=
  volume_axisBox_ne_top _ _

/-- An open centered cube has positive volume at positive half-side. -/
theorem volume_centeredAxisCube_pos {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < volume (centeredAxisCube x₀ R) := by
  apply volume_axisBox_pos
  intro i
  linarith

/-- The real volume of an open centered cube is positive at positive
half-side. This is the form used by normalized averages. -/
theorem volume_centeredAxisCube_toReal_pos {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < (volume (centeredAxisCube x₀ R)).toReal := by
  rw [volume_centeredAxisCube_toReal x₀ hR.le]
  exact pow_pos (by positivity) _

/-- Open and closed centered axis cubes agree up to a volume-null boundary.

This is the native-vector bridge used to pass between open domains and closed
inner sets in energy iterations. -/
theorem centeredAxisCube_ae_eq_closedCenteredAxisCube {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    centeredAxisCube x₀ R =ᵐ[volume]
      closedCenteredAxisCube x₀ R := by
  exact Measure.pi_Ioo_ae_eq_pi_Icc

/-- The exact real volume of a closed centered cube of half-side `R`. -/
theorem volume_closedCenteredAxisCube_toReal {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    (volume (closedCenteredAxisCube x₀ R)).toReal =
      (2 * R) ^ d := by
  rw [← (centeredAxisCube_ae_eq_closedCenteredAxisCube x₀ R).measure_eq]
  exact volume_centeredAxisCube_toReal x₀ hR

/-- The exact extended-real volume of a closed centered cube of nonnegative
half-side `R`. -/
theorem volume_closedCenteredAxisCube {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedCenteredAxisCube x₀ R) =
      ENNReal.ofReal ((2 * R) ^ d) := by
  rw [← (centeredAxisCube_ae_eq_closedCenteredAxisCube x₀ R).measure_eq]
  exact volume_centeredAxisCube x₀ hR

/-- A closed centered cube has finite volume at every scale. -/
theorem volume_closedCenteredAxisCube_ne_top {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    volume (closedCenteredAxisCube x₀ R) ≠ ∞ := by
  rw [← (centeredAxisCube_ae_eq_closedCenteredAxisCube x₀ R).measure_eq]
  exact volume_centeredAxisCube_ne_top x₀ R

/-- A closed centered cube has positive volume at positive half-side. -/
theorem volume_closedCenteredAxisCube_pos {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < volume (closedCenteredAxisCube x₀ R) := by
  rw [← (centeredAxisCube_ae_eq_closedCenteredAxisCube x₀ R).measure_eq]
  exact volume_centeredAxisCube_pos x₀ hR

/-- The real volume of a closed centered cube is positive at positive
half-side. -/
theorem volume_closedCenteredAxisCube_toReal_pos {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < (volume (closedCenteredAxisCube x₀ R)).toReal := by
  rw [volume_closedCenteredAxisCube_toReal x₀ hR.le]
  exact pow_pos (by positivity) _

/-- The ratio of the volumes of two positive-radius open centered cubes is
the corresponding radius ratio to the dimension, independently of centers. -/
theorem volume_centeredAxisCube_toReal_div_eq_div_pow {d : ℕ}
    (x y : Vec d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (volume (centeredAxisCube x R)).toReal /
        (volume (centeredAxisCube y r)).toReal =
      (R / r) ^ d := by
  rw [volume_centeredAxisCube_toReal x hR.le,
    volume_centeredAxisCube_toReal y hr.le, ← div_pow]
  congr 1
  field_simp

/-- The ratio of the volumes of two positive-radius closed centered cubes is
the corresponding radius ratio to the dimension, independently of centers. -/
theorem volume_closedCenteredAxisCube_toReal_div_eq_div_pow {d : ℕ}
    (x y : Vec d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (volume (closedCenteredAxisCube x R)).toReal /
        (volume (closedCenteredAxisCube y r)).toReal =
      (R / r) ^ d := by
  rw [volume_closedCenteredAxisCube_toReal x hR.le,
    volume_closedCenteredAxisCube_toReal y hr.le, ← div_pow]
  congr 1
  field_simp

end PDE
