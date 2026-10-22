module

public import PDEFoundation.Measure.GoodSquareRadiusFubini

/-!
# Scalar Fubini estimates on enlarged square loops

This module supplies the scalar counterpart of the tangential boundary-energy
calculation used for good square radii.  The side segments are deliberately
enlarged to the fixed interval of half-length `2 * r`; this makes their
radius average an ordinary Fubini calculation over the four shell strips.

The estimates are stated for arbitrary scalar `L²` data on the outer square,
so they can be applied directly to differences of smooth Sobolev
approximants.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The scalar `L²` energy on the four enlarged sides of the square of
half-side `ρ`.  Each side is integrated over the fixed outer interval of
half-length `2 * r`. -/
def enlargedSquareSideScalarEnergy
    (f : Vec 2 → ℝ) (x₀ : Vec 2) (r ρ : ℝ) : ℝ :=
  (∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
      f (squarePoint (x₀ 0 + ρ) t) ^ 2) +
  (∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
      f (squarePoint (x₀ 0 - ρ) t) ^ 2) +
  (∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
      f (squarePoint t (x₀ 1 + ρ)) ^ 2) +
  ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
      f (squarePoint t (x₀ 1 - ρ)) ^ 2

/-- The scalar `L²` energy on the dyadic square shell. -/
def squareShellScalarEnergy
    (f : Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ :=
  ∫ x in dyadicSquareShell x₀ r, f x ^ 2

/-- Scalar four-side energy is nonnegative at every radius. -/
theorem enlargedSquareSideScalarEnergy_nonneg
    (f : Vec 2 → ℝ) (x₀ : Vec 2) (r ρ : ℝ) :
    0 ≤ enlargedSquareSideScalarEnergy f x₀ r ρ := by
  unfold enlargedSquareSideScalarEnergy
  have hRight : 0 ≤
      ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        f (squarePoint (x₀ 0 + ρ) t) ^ 2 :=
    integral_nonneg fun t => sq_nonneg _
  have hLeft : 0 ≤
      ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        f (squarePoint (x₀ 0 - ρ) t) ^ 2 :=
    integral_nonneg fun t => sq_nonneg _
  have hTop : 0 ≤
      ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        f (squarePoint t (x₀ 1 + ρ)) ^ 2 :=
    integral_nonneg fun t => sq_nonneg _
  have hBottom : 0 ≤
      ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        f (squarePoint t (x₀ 1 - ρ)) ^ 2 :=
    integral_nonneg fun t => sq_nonneg _
  positivity

/-- Scalar shell energy is nonnegative. -/
theorem squareShellScalarEnergy_nonneg
    (f : Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) :
    0 ≤ squareShellScalarEnergy f x₀ r :=
  integral_nonneg fun x => sq_nonneg (f x)

private theorem integralOn_Ioo_comp_add_left
    {H : ℝ → ℝ} {a b c : ℝ} :
    (∫ ρ in Ioo a b, H (c + ρ)) =
      ∫ s in Ioo (c + a) (c + b), H s := by
  let I : Set ℝ := Ioo a b
  let J : Set ℝ := Ioo (c + a) (c + b)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hJ : MeasurableSet J := measurableSet_Ioo
  have hpres : MeasurePreserving (fun x : ℝ => c + x) volume volume :=
    measurePreserving_add_left volume c
  calc
    (∫ ρ in I, H (c + ρ)) = ∫ ρ, I.indicator (fun ρ => H (c + ρ)) ρ := by
      rw [integral_indicator hI]
    _ = ∫ ρ, J.indicator H (c + ρ) := by
      apply integral_congr_ae
      filter_upwards with ρ
      by_cases hρ : ρ ∈ I
      · have hcρ : c + ρ ∈ J := by
          change a < ρ ∧ ρ < b at hρ
          change c + a < c + ρ ∧ c + ρ < c + b
          constructor <;> linarith
        simp [Set.indicator_of_mem hρ, Set.indicator_of_mem hcρ]
      · have hcρ : c + ρ ∉ J := by
          intro hcρ
          apply hρ
          change c + a < c + ρ ∧ c + ρ < c + b at hcρ
          change a < ρ ∧ ρ < b
          constructor <;> linarith
        simp [Set.indicator_of_notMem hρ, Set.indicator_of_notMem hcρ]
    _ = ∫ s, J.indicator H s := by
      exact hpres.integral_comp' (f := MeasurableEquiv.addLeft c) _
    _ = ∫ s in J, H s := integral_indicator hJ

private theorem integralOn_Ioo_comp_sub_left
    {H : ℝ → ℝ} {a b c : ℝ} :
    (∫ ρ in Ioo a b, H (c - ρ)) =
      ∫ s in Ioo (c - b) (c - a), H s := by
  let I : Set ℝ := Ioo a b
  let J : Set ℝ := Ioo (c - b) (c - a)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hJ : MeasurableSet J := measurableSet_Ioo
  have hpres : MeasurePreserving (fun x : ℝ => c - x) volume volume := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using!
      (measurePreserving_add_left volume c).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  calc
    (∫ ρ in I, H (c - ρ)) = ∫ ρ, I.indicator (fun ρ => H (c - ρ)) ρ := by
      rw [integral_indicator hI]
    _ = ∫ ρ, J.indicator H (c - ρ) := by
      apply integral_congr_ae
      filter_upwards with ρ
      by_cases hρ : ρ ∈ I
      · have hcρ : c - ρ ∈ J := by
          change a < ρ ∧ ρ < b at hρ
          change c - b < c - ρ ∧ c - ρ < c - a
          constructor <;> linarith
        simp [Set.indicator_of_mem hρ, Set.indicator_of_mem hcρ]
      · have hcρ : c - ρ ∉ J := by
          intro hcρ
          apply hρ
          change c - b < c - ρ ∧ c - ρ < c - a at hcρ
          change a < ρ ∧ ρ < b
          constructor <;> linarith
        simp [Set.indicator_of_notMem hρ, Set.indicator_of_notMem hcρ]
    _ = ∫ s, J.indicator H s := by
      exact hpres.integral_comp' (f := MeasurableEquiv.subLeft c) _
    _ = ∫ s in J, H s := integral_indicator hJ

private theorem integrableOn_Ioo_comp_add_left
    {H : ℝ → ℝ} {a b c : ℝ}
    (hH : IntegrableOn H (Ioo (c + a) (c + b))) :
    IntegrableOn (fun ρ => H (c + ρ)) (Ioo a b) := by
  have hpres : MeasurePreserving (fun x : ℝ => c + x) volume volume :=
    measurePreserving_add_left volume c
  have hpreimage : (fun x : ℝ => c + x) ⁻¹' Ioo (c + a) (c + b) = Ioo a b := by
    ext x
    change (c + a < c + x ∧ c + x < c + b) ↔ a < x ∧ x < b
    constructor <;> intro hx <;> constructor <;> linarith
  have htransport :=
    (hpres.integrableOn_comp_preimage
      (MeasurableEquiv.addLeft c).measurableEmbedding).mpr hH
  rw [hpreimage] at htransport
  simpa only [Function.comp_apply] using! htransport

private theorem integrableOn_Ioo_comp_sub_left
    {H : ℝ → ℝ} {a b c : ℝ}
    (hH : IntegrableOn H (Ioo (c - b) (c - a))) :
    IntegrableOn (fun ρ => H (c - ρ)) (Ioo a b) := by
  have hpres : MeasurePreserving (fun x : ℝ => c - x) volume volume := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using!
      (measurePreserving_add_left volume c).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpreimage : (fun x : ℝ => c - x) ⁻¹' Ioo (c - b) (c - a) = Ioo a b := by
    ext x
    change (c - b < c - x ∧ c - x < c - a) ↔ a < x ∧ x < b
    constructor <;> intro hx <;> constructor <;> linarith
  have htransport :=
    (hpres.integrableOn_comp_preimage
      (MeasurableEquiv.subLeft c).measurableEmbedding).mpr hH
  rw [hpreimage] at htransport
  simpa only [Function.comp_apply] using! htransport

private theorem integrableOn_sq_of_memL2On
    {f : Vec 2 → ℝ} {U S : Set (Vec 2)}
    (hf : MemL2On U f) (hSU : S ⊆ U) :
    IntegrableOn (fun x => f x ^ 2) S := by
  simpa only [pow_two] using
    (integrableOn_mul_of_memL2On hf hf).mono_set hSU

private theorem scalar_boundary_fubini
    {f : Vec 2 → ℝ} {x₀ : Vec 2} {r : ℝ}
    (hf : MemL2On (centeredAxisCube x₀ (2 * r)) f) :
    IntegrableOn (enlargedSquareSideScalarEnergy f x₀ r) (Ioo r (2 * r)) ∧
      (∫ ρ in Ioo r (2 * r), enlargedSquareSideScalarEnergy f x₀ r ρ) =
        (((∫ x in dyadicSquareShellRight x₀ r, f x ^ 2) +
          ∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2) +
        ∫ x in dyadicSquareShellTop x₀ r, f x ^ 2) +
          ∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2 := by
  have hRightOuter : dyadicSquareShellRight x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellRight_subset x₀ r hx).1
  have hLeftOuter : dyadicSquareShellLeft x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellLeft_subset x₀ r hx).1
  have hTopOuter : dyadicSquareShellTop x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellTop_subset x₀ r hx).1
  have hBottomOuter : dyadicSquareShellBottom x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellBottom_subset x₀ r hx).1
  have hRight : IntegrableOn (fun x => f x ^ 2) (dyadicSquareShellRight x₀ r) :=
    integrableOn_sq_of_memL2On hf hRightOuter
  have hLeft : IntegrableOn (fun x => f x ^ 2) (dyadicSquareShellLeft x₀ r) :=
    integrableOn_sq_of_memL2On hf hLeftOuter
  have hTop : IntegrableOn (fun x => f x ^ 2) (dyadicSquareShellTop x₀ r) :=
    integrableOn_sq_of_memL2On hf hTopOuter
  have hBottom : IntegrableOn (fun x => f x ^ 2) (dyadicSquareShellBottom x₀ r) :=
    integrableOn_sq_of_memL2On hf hBottomOuter
  have hRightRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        f (squarePoint (x₀ 0 + ρ) t) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_add_left (c := x₀ 0)
        (integrableOn_axisBox_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellRight] using hRight)))
  have hLeftRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        f (squarePoint (x₀ 0 - ρ) t) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_sub_left (c := x₀ 0)
        (integrableOn_axisBox_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellLeft] using hLeft)))
  have hTopRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        f (squarePoint t (x₀ 1 + ρ)) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_add_left (c := x₀ 1)
        (integrableOn_axisBox_outerSecond_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellTop] using hTop)))
  have hBottomRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        f (squarePoint t (x₀ 1 - ρ)) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_sub_left (c := x₀ 1)
        (integrableOn_axisBox_outerSecond_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellBottom] using hBottom)))
  have hRightEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        f (squarePoint (x₀ 0 + ρ) t) ^ 2) =
        ∫ x in dyadicSquareShellRight x₀ r, f x ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f (squarePoint (x₀ 0 + ρ) t) ^ 2) =
          ∫ s in Ioo (x₀ 0 + r) (x₀ 0 + 2 * r),
            ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
              f (squarePoint s t) ^ 2 :=
        integralOn_Ioo_comp_add_left (a := r) (b := 2 * r) (c := x₀ 0)
          (H := fun s => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
            f (squarePoint s t) ^ 2)
      _ = ∫ x in dyadicSquareShellRight x₀ r, f x ^ 2 := by
        simpa only [dyadicSquareShellRight] using
          (integralOn_axisBox_eq_integral_squarePoint hRight).symm
  have hLeftEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        f (squarePoint (x₀ 0 - ρ) t) ^ 2) =
        ∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          f (squarePoint (x₀ 0 - ρ) t) ^ 2) =
          ∫ s in Ioo (x₀ 0 - 2 * r) (x₀ 0 - r),
            ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
              f (squarePoint s t) ^ 2 :=
        integralOn_Ioo_comp_sub_left (a := r) (b := 2 * r) (c := x₀ 0)
          (H := fun s => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
            f (squarePoint s t) ^ 2)
      _ = ∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2 := by
        simpa only [dyadicSquareShellLeft] using
          (integralOn_axisBox_eq_integral_squarePoint hLeft).symm
  have hTopEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        f (squarePoint t (x₀ 1 + ρ)) ^ 2) =
        ∫ x in dyadicSquareShellTop x₀ r, f x ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f (squarePoint t (x₀ 1 + ρ)) ^ 2) =
          ∫ s in Ioo (x₀ 1 + r) (x₀ 1 + 2 * r),
            ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
              f (squarePoint t s) ^ 2 :=
        integralOn_Ioo_comp_add_left (a := r) (b := 2 * r) (c := x₀ 1)
          (H := fun s => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
            f (squarePoint t s) ^ 2)
      _ = ∫ x in dyadicSquareShellTop x₀ r, f x ^ 2 := by
        simpa only [dyadicSquareShellTop] using
          (integralOn_axisBox_eq_integral_outerSecond_squarePoint hTop).symm
  have hBottomEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        f (squarePoint t (x₀ 1 - ρ)) ^ 2) =
        ∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          f (squarePoint t (x₀ 1 - ρ)) ^ 2) =
          ∫ s in Ioo (x₀ 1 - 2 * r) (x₀ 1 - r),
            ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
              f (squarePoint t s) ^ 2 :=
        integralOn_Ioo_comp_sub_left (a := r) (b := 2 * r) (c := x₀ 1)
          (H := fun s => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
            f (squarePoint t s) ^ 2)
      _ = ∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2 := by
        simpa only [dyadicSquareShellBottom] using
          (integralOn_axisBox_eq_integral_outerSecond_squarePoint hBottom).symm
  let R : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
    f (squarePoint (x₀ 0 + ρ) t) ^ 2
  let L : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
    f (squarePoint (x₀ 0 - ρ) t) ^ 2
  let T : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
    f (squarePoint t (x₀ 1 + ρ)) ^ 2
  let B : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
    f (squarePoint t (x₀ 1 - ρ)) ^ 2
  have hR : IntegrableOn R (Ioo r (2 * r)) := by
    simpa only [R] using hRightRadius
  have hL : IntegrableOn L (Ioo r (2 * r)) := by
    simpa only [L] using hLeftRadius
  have hT : IntegrableOn T (Ioo r (2 * r)) := by
    simpa only [T] using hTopRadius
  have hB : IntegrableOn B (Ioo r (2 * r)) := by
    simpa only [B] using hBottomRadius
  have hEnergy : enlargedSquareSideScalarEnergy f x₀ r = ((R + L) + T) + B := by
    funext ρ
    rfl
  have hREq : (∫ ρ in Ioo r (2 * r), R ρ) =
      ∫ x in dyadicSquareShellRight x₀ r, f x ^ 2 := by
    simpa only [R] using hRightEq
  have hLEq : (∫ ρ in Ioo r (2 * r), L ρ) =
      ∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2 := by
    simpa only [L] using hLeftEq
  have hTEq : (∫ ρ in Ioo r (2 * r), T ρ) =
      ∫ x in dyadicSquareShellTop x₀ r, f x ^ 2 := by
    simpa only [T] using hTopEq
  have hBEq : (∫ ρ in Ioo r (2 * r), B ρ) =
      ∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2 := by
    simpa only [B] using hBottomEq
  constructor
  · rw [hEnergy]
    exact ((hR.add hL).add hT).add hB
  · calc
      (∫ ρ in Ioo r (2 * r), enlargedSquareSideScalarEnergy f x₀ r ρ) =
          ∫ ρ in Ioo r (2 * r), (((R + L) + T) + B) ρ := by
            rw [hEnergy]
      _ = (((∫ ρ in Ioo r (2 * r), R ρ) + ∫ ρ in Ioo r (2 * r), L ρ) +
          ∫ ρ in Ioo r (2 * r), T ρ) + ∫ ρ in Ioo r (2 * r), B ρ := by
            rw [show (∫ ρ in Ioo r (2 * r), (((R + L) + T) + B) ρ) =
                (∫ ρ in Ioo r (2 * r), ((R + L) + T) ρ) +
                  ∫ ρ in Ioo r (2 * r), B ρ by
                  simpa only [Pi.add_apply] using integral_add ((hR.add hL).add hT) hB,
              show (∫ ρ in Ioo r (2 * r), ((R + L) + T) ρ) =
                (∫ ρ in Ioo r (2 * r), (R + L) ρ) +
                  ∫ ρ in Ioo r (2 * r), T ρ by
                  simpa only [Pi.add_apply] using integral_add (hR.add hL) hT,
              show (∫ ρ in Ioo r (2 * r), (R + L) ρ) =
                (∫ ρ in Ioo r (2 * r), R ρ) + ∫ ρ in Ioo r (2 * r), L ρ by
                  simpa only [Pi.add_apply] using integral_add hR hL]
      _ = (((∫ x in dyadicSquareShellRight x₀ r, f x ^ 2) +
            ∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2) +
          ∫ x in dyadicSquareShellTop x₀ r, f x ^ 2) +
            ∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2 := by
            rw [hREq, hLEq, hTEq, hBEq]

/-- Scalar enlarged-side energy is integrable in the square radius whenever
the scalar field is `L²` on the outer square. -/
theorem integrableOn_enlargedSquareSideScalarEnergy_of_memL2On
    {f : Vec 2 → ℝ} {x₀ : Vec 2} {r : ℝ}
    (hf : MemL2On (centeredAxisCube x₀ (2 * r)) f) :
    IntegrableOn (enlargedSquareSideScalarEnergy f x₀ r) (Ioo r (2 * r)) :=
  (scalar_boundary_fubini hf).1

/-- Exact Fubini decomposition of scalar enlarged-side energy into the four
shell-strip `L²` integrals. -/
theorem integral_enlargedSquareSideScalarEnergy_eq_shellStrips
    {f : Vec 2 → ℝ} {x₀ : Vec 2} {r : ℝ}
    (hf : MemL2On (centeredAxisCube x₀ (2 * r)) f) :
    (∫ ρ in Ioo r (2 * r), enlargedSquareSideScalarEnergy f x₀ r ρ) =
      (((∫ x in dyadicSquareShellRight x₀ r, f x ^ 2) +
        ∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2) +
      ∫ x in dyadicSquareShellTop x₀ r, f x ^ 2) +
        ∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2 :=
  (scalar_boundary_fubini hf).2

/-- The radius average of scalar enlarged-side energy is bounded by four
times the scalar shell energy.  The factor four is the explicit overlap loss
from controlling each of the four strips by the whole shell. -/
theorem integral_enlargedSquareSideScalarEnergy_le_four_mul_squareShellScalarEnergy
    {f : Vec 2 → ℝ} {x₀ : Vec 2} {r : ℝ}
    (hf : MemL2On (centeredAxisCube x₀ (2 * r)) f) :
    (∫ ρ in Ioo r (2 * r), enlargedSquareSideScalarEnergy f x₀ r ρ) ≤
      4 * squareShellScalarEnergy f x₀ r := by
  have hShell : IntegrableOn (fun x => f x ^ 2) (dyadicSquareShell x₀ r) :=
    integrableOn_sq_of_memL2On hf (fun x hx => hx.1)
  have hRight : (∫ x in dyadicSquareShellRight x₀ r, f x ^ 2) ≤
      squareShellScalarEnergy f x₀ r := by
    exact setIntegral_mono_set hShell
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall fun x hx => dyadicSquareShellRight_subset x₀ r hx)
  have hLeft : (∫ x in dyadicSquareShellLeft x₀ r, f x ^ 2) ≤
      squareShellScalarEnergy f x₀ r := by
    exact setIntegral_mono_set hShell
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall fun x hx => dyadicSquareShellLeft_subset x₀ r hx)
  have hTop : (∫ x in dyadicSquareShellTop x₀ r, f x ^ 2) ≤
      squareShellScalarEnergy f x₀ r := by
    exact setIntegral_mono_set hShell
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall fun x hx => dyadicSquareShellTop_subset x₀ r hx)
  have hBottom : (∫ x in dyadicSquareShellBottom x₀ r, f x ^ 2) ≤
      squareShellScalarEnergy f x₀ r := by
    exact setIntegral_mono_set hShell
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall fun x hx => dyadicSquareShellBottom_subset x₀ r hx)
  rw [integral_enlargedSquareSideScalarEnergy_eq_shellStrips hf]
  linarith

end

end PDE
