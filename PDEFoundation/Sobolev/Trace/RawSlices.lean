module

public import PDEFoundation.Measure.AxisBoxSlice

/-!
# Raw `L²` slices of enlarged square sides

This module isolates the Fubini layer used by the square-trace construction.
It supplies genuine one-dimensional `L²` membership for the raw restrictions
of a scalar function and the tangential coordinate of a vector field.  No
Sobolev approximation or good-radius selection is used here.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The four raw, fixed-length side slices used by the enlarged-square trace
construction are honest scalar `L²` functions. -/
def HasRawEnlargedSquareSideSlices
    (f : Vec 2 → ℝ) (x₀ : Vec 2) (r ρ : ℝ) : Prop :=
  MemLp (fun t => f (squarePoint (x₀ 0 + ρ) t)) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))) ∧
    MemLp (fun t => f (squarePoint (x₀ 0 - ρ) t)) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))) ∧
    MemLp (fun t => f (squarePoint t (x₀ 1 + ρ))) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))) ∧
    MemLp (fun t => f (squarePoint t (x₀ 1 - ρ))) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r)))

/-- The raw tangential components of a vector field on the four enlarged
square sides are genuine scalar `L²` functions.  The vertical sides use
coordinate `1` and the horizontal sides coordinate `0`, exactly as in
`enlargedSquareSideTangentialEnergy`. -/
def HasRawEnlargedSquareTangentialSlices
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r ρ : ℝ) : Prop :=
  MemLp (fun t => g (squarePoint (x₀ 0 + ρ) t) 1) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))) ∧
    MemLp (fun t => g (squarePoint (x₀ 0 - ρ) t) 1) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))) ∧
    MemLp (fun t => g (squarePoint t (x₀ 1 + ρ)) 0) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))) ∧
    MemLp (fun t => g (squarePoint t (x₀ 1 - ρ)) 0) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r)))

/-- At an intermediate radius, the actual four-side tangential energy is no
larger than the fixed-width enlarged energy used in radius selection. -/
theorem squareSideTangentialEnergy_le_enlarged
    {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r ρ : ℝ}
    (hρ : ρ ∈ Ioo r (2 * r))
    (hg : HasRawEnlargedSquareTangentialSlices g x₀ r ρ) :
    squareSideTangentialEnergy g x₀ ρ ≤
      enlargedSquareSideTangentialEnergy g x₀ r ρ := by
  have hVertical :
      Icc (x₀ 1 - ρ) (x₀ 1 + ρ) ⊆
        Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hHorizontal :
      Icc (x₀ 0 - ρ) (x₀ 0 + ρ) ⊆
        Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hRightIntegrable : IntegrableOn
      (fun t => (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2)
      (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r)) volume := by
    simpa only [IntegrableOn] using hg.1.integrable_sq
  have hLeftIntegrable : IntegrableOn
      (fun t => (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2)
      (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r)) volume := by
    simpa only [IntegrableOn] using hg.2.1.integrable_sq
  have hTopIntegrable : IntegrableOn
      (fun t => (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2)
      (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r)) volume := by
    simpa only [IntegrableOn] using hg.2.2.1.integrable_sq
  have hBottomIntegrable : IntegrableOn
      (fun t => (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2)
      (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r)) volume := by
    simpa only [IntegrableOn] using hg.2.2.2.integrable_sq
  have hRight :
      (∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2) ≤
      ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2 :=
    setIntegral_mono_set hRightIntegrable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hVertical)
  have hLeft :
      (∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
        (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2) ≤
      ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2 :=
    setIntegral_mono_set hLeftIntegrable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hVertical)
  have hTop :
      (∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2) ≤
      ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2 :=
    setIntegral_mono_set hTopIntegrable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hHorizontal)
  have hBottom :
      (∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
        (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2) ≤
      ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2 :=
    setIntegral_mono_set hBottomIntegrable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hHorizontal)
  unfold squareSideTangentialEnergy enlargedSquareSideTangentialEnergy
  linarith

/-- Raw vertical and horizontal enlarged-square slices of an `L²` function
are genuine `L²` functions for almost every radius.  This is the translated
and reflected form of the axis-box Fubini theorem used by square traces. -/
theorem ae_memLp_enlargedSquare_raw_slices_of_memL2On
    {f : Vec 2 → ℝ} {x₀ : Vec 2} {r : ℝ}
    (hf : MemL2On (centeredAxisCube x₀ (2 * r)) f) :
    ∀ᵐ ρ ∂volume.restrict (Ioo r (2 * r)),
      HasRawEnlargedSquareSideSlices f x₀ r ρ := by
  have hf' : MemL2On
      (axisBox ![x₀ 0 - 2 * r, x₀ 1 - 2 * r]
        ![x₀ 0 + 2 * r, x₀ 1 + 2 * r]) f := by
    have hlower :
        (fun i : Fin 2 => x₀ i - 2 * r) =
          ![x₀ 0 - 2 * r, x₀ 1 - 2 * r] := by
      funext i
      fin_cases i <;> rfl
    have hupper :
        (fun i : Fin 2 => x₀ i + 2 * r) =
          ![x₀ 0 + 2 * r, x₀ 1 + 2 * r] := by
      funext i
      fin_cases i <;> rfl
    simpa only [centeredAxisCube, hlower, hupper] using hf
  have hvertical := memLp_axisBox_slice_second_ae hf'
  have hhorizontal := memLp_axisBox_slice_first_ae hf'
  have hplus : Measure.QuasiMeasurePreserving
      (fun ρ : ℝ => x₀ 0 + ρ)
      (volume.restrict (Ioo r (2 * r)))
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))) := by
    apply (measurePreserving_add_left volume (x₀ 0)).quasiMeasurePreserving.restrict
    intro ρ hρ
    change r < ρ ∧ ρ < 2 * r at hρ
    change x₀ 0 - 2 * r < x₀ 0 + ρ ∧ x₀ 0 + ρ < x₀ 0 + 2 * r
    constructor <;> linarith
  have hminus : Measure.QuasiMeasurePreserving
      (fun ρ : ℝ => x₀ 0 - ρ)
      (volume.restrict (Ioo r (2 * r)))
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))) := by
    have hpres : MeasurePreserving (fun ρ : ℝ => x₀ 0 - ρ) volume volume := by
      simpa only [Function.comp_apply, sub_eq_add_neg] using!
        (measurePreserving_add_left volume (x₀ 0)).comp
          (Measure.measurePreserving_neg (volume : Measure ℝ))
    apply hpres.quasiMeasurePreserving.restrict
    intro ρ hρ
    change r < ρ ∧ ρ < 2 * r at hρ
    change x₀ 0 - 2 * r < x₀ 0 - ρ ∧ x₀ 0 - ρ < x₀ 0 + 2 * r
    constructor <;> linarith
  have htop : Measure.QuasiMeasurePreserving
      (fun ρ : ℝ => x₀ 1 + ρ)
      (volume.restrict (Ioo r (2 * r)))
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))) := by
    apply (measurePreserving_add_left volume (x₀ 1)).quasiMeasurePreserving.restrict
    intro ρ hρ
    change r < ρ ∧ ρ < 2 * r at hρ
    change x₀ 1 - 2 * r < x₀ 1 + ρ ∧ x₀ 1 + ρ < x₀ 1 + 2 * r
    constructor <;> linarith
  have hbottom : Measure.QuasiMeasurePreserving
      (fun ρ : ℝ => x₀ 1 - ρ)
      (volume.restrict (Ioo r (2 * r)))
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))) := by
    have hpres : MeasurePreserving (fun ρ : ℝ => x₀ 1 - ρ) volume volume := by
      simpa only [Function.comp_apply, sub_eq_add_neg] using!
        (measurePreserving_add_left volume (x₀ 1)).comp
          (Measure.measurePreserving_neg (volume : Measure ℝ))
    apply hpres.quasiMeasurePreserving.restrict
    intro ρ hρ
    change r < ρ ∧ ρ < 2 * r at hρ
    change x₀ 1 - 2 * r < x₀ 1 - ρ ∧ x₀ 1 - ρ < x₀ 1 + 2 * r
    constructor <;> linarith
  filter_upwards [hplus.ae hvertical, hminus.ae hvertical,
    htop.ae hhorizontal, hbottom.ae hhorizontal] with ρ hplus hminus htop hbottom
  exact ⟨hplus, hminus, htop, hbottom⟩

/-- The four raw tangential restrictions are genuine `L²` functions
for almost every enlarged-square radius.  This is a coordinatewise use of
the scalar axis-box slicing theorem, with no trace regularity assumed. -/
theorem ae_memLp_enlargedSquare_raw_tangential_slices_of_memVectorL2On
    {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    (hg : ∀ i, MemL2On (centeredAxisCube x₀ (2 * r)) (fun x => g x i)) :
    ∀ᵐ ρ ∂volume.restrict (Ioo r (2 * r)),
      HasRawEnlargedSquareTangentialSlices g x₀ r ρ := by
  filter_upwards [ae_memLp_enlargedSquare_raw_slices_of_memL2On (hg 1),
    ae_memLp_enlargedSquare_raw_slices_of_memL2On (hg 0)] with ρ hvertical hhorizontal
  exact ⟨hvertical.1, hvertical.2.1, hhorizontal.2.2.1, hhorizontal.2.2.2⟩

end

end PDE
