module

public import EllipticRegularity.Parabolic.Moser.SliceOrder

/-!
# Time-local order transfer for parabolic energy functions

Local maximum and weak-Harnack estimates control different time cylinders.
This file restricts a `ParH1Function` to a measurable time subset and proves
the endpoint transfer for separate upper and lower space-time bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Moser

/-- Restrict a parabolic energy function to a smaller time set. -/
def restrictParH1TimeSet {d : ℕ} {U : Set (Vec d)} {I J : Set ℝ}
    (u : ParH1Function U I) (hJI : J ⊆ I) : ParH1Function U J where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2.mono_measure
    (Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl)
  gradMemL2 i := (u.gradMemL2 i).mono_measure
    (Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl)
  sliceWeakGradient := by
    have hmeas : volume.restrict J ≤ volume.restrict I :=
      Measure.restrict_mono hJI le_rfl
    exact ae_mono hmeas u.sliceWeakGradient
  sliceL2loc t ht K hK hKU := u.sliceL2loc t (hJI ht) K hK hKU
  weakCont ψ hψ := (u.weakCont ψ hψ).mono hJI

/-- Transfer upper and lower estimates on two possibly different time
subsets to their endpoint spatial slices. -/
theorem parH1_two_time_slice_harnack_of_separate_time_bounds
    {d : ℕ} {U : Set (Vec d)} {I J₀ J₁ : Set ℝ}
    (hJ₀I : J₀ ⊆ I) (hJ₁I : J₁ ⊆ I)
    (hJ₀meas : MeasurableSet J₀) (hJ₁meas : MeasurableSet J₁)
    (u : ParH1Function U I) {M m H : ℝ}
    (hH : 0 ≤ H) (hMm : M ≤ H * m)
    (hupper : ∀ᵐ z ∂(volume.restrict (U ×ˢ J₀)), u.toFun z ≤ M)
    (hlower : ∀ᵐ z ∂(volume.restrict (U ×ˢ J₁)), m ≤ u.toFun z)
    {K₀ K₁ : Set (Vec d)} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hK₀U : K₀ ⊆ U) (hK₁U : K₁ ⊆ U)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ interior J₀) (ht₁ : t₁ ∈ interior J₁) :
    essSup (fun x => ENNReal.ofReal (u.toFun (x, t₀))) (volumeOn K₀) ≤
      ENNReal.ofReal H *
        essInf (fun x => ENNReal.ofReal (u.toFun (x, t₁))) (volumeOn K₁) := by
  have hsup := parH1_slice_essSup_ofReal_le_of_ae_spaceTime_le
    hJ₀meas (restrictParH1TimeSet u hJ₀I) hupper hK₀ hK₀U t₀ ht₀
  have hinf := parH1_slice_essInf_ofReal_ge_of_ae_spaceTime_ge
    hJ₁meas (restrictParH1TimeSet u hJ₁I) hlower hK₁ hK₁U t₁ ht₁
  calc
    essSup (fun x => ENNReal.ofReal (u.toFun (x, t₀))) (volumeOn K₀) ≤
        ENNReal.ofReal M := hsup
    _ ≤ ENNReal.ofReal (H * m) := ENNReal.ofReal_le_ofReal hMm
    _ = ENNReal.ofReal H * ENNReal.ofReal m := ENNReal.ofReal_mul hH
    _ ≤ ENNReal.ofReal H *
        essInf (fun x => ENNReal.ofReal (u.toFun (x, t₁))) (volumeOn K₁) :=
      mul_le_mul_of_nonneg_left hinf (by positivity)

end PDE.Parabolic.Moser
