module

public import EllipticRegularity.Parabolic.Rescale.AffineEnergy
public import EllipticRegularity.Parabolic.Rescale.AffineTest

/-!
# Parabolic rescaling to the unit cylinder

`exists_unit_rescaling`: a weak solution of `∂ₜu - ∇·(a∇u) = 0` in `B(c, r) × I'` with
`(T₀ - r², T₀] ⊆ I'` rescales, via `Φ(y, s) = (c + r • y, T₀ + r² s)`, to a weak solution on the
unit cylinder `B₁ × (-1, 0]` with the same ellipticity constants.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

variable {d : ℕ}

theorem parWeakIntegrand_rescale (a : ParCoeffField d) (c : Vec d) {r : ℝ} (hr : 0 < r) (T₀ : ℝ)
    {I' : Set ℝ} (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I') (u : ParH1Function (euclideanBall c r) I')
    {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) :
    parWeakIntegrand (fun z => a (cylMap c r T₀ z)) (rescaleParH1 c hr T₀ hI' u)
        (φ ∘ cylMap c r T₀) z =
      r ^ 2 * parWeakIntegrand a u φ (cylMap c r T₀ z) := by
  unfold parWeakIntegrand
  rw [parTimeDeriv_comp_cylMap c r T₀ hφ, parSpaceGrad_comp_cylMap c r T₀ hφ]
  simp only [rescaleParH1, matVecMul_smul', vecDot_smul_smul']
  ring

theorem parWeakIntegrand_eq_zero_of_notMem_tsupport (a : ParCoeffField d) {U : Set (Vec d)}
    {I : Set ℝ} (u : ParH1Function U I) {φ : Vec d × ℝ → ℝ} {w : Vec d × ℝ}
    (hw : w ∉ tsupport φ) : parWeakIntegrand a u φ w = 0 := by
  have h : fderiv ℝ φ w = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hw
  have h1 : parTimeDeriv φ w = 0 := by simp [parTimeDeriv, h]
  have h2 : parSpaceGrad φ w = 0 := by
    funext i; simp [parSpaceGrad, h]
  simp [parWeakIntegrand, h1, h2, vecDot]

theorem isParabolicCoeff_rescale {Lam : ℝ} (a : ParCoeffField d) (c : Vec d) {r : ℝ} (hr : 0 < r)
    (T₀ : ℝ) {I' : Set ℝ} (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I')
    (ha : IsParabolicCoeff 1 Lam a (euclideanBall c r) I') :
    IsParabolicCoeff 1 Lam (fun z => a (cylMap c r T₀ z)) (euclideanBall (0 : Vec d) 1)
      (Ioc (-1 : ℝ) 0) := by
  have hμ₀ : (volume : Measure (Vec d × ℝ)).restrict (euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀) ≤
      (volume : Measure (Vec d × ℝ)).restrict (euclideanBall c r ×ˢ I') :=
    Measure.restrict_mono (prod_mono subset_rfl hI') le_rfl
  refine ⟨fun i j => ?_, ?_⟩
  · exact aemeasurable_comp_of_map_eq_smul (cylMap_measurableEmbedding c hr T₀)
      (map_restrict_unitCylinder c hr T₀) ((ha.measurable i j).mono_measure hμ₀)
  · exact ae_comp_of_map_eq_smul (cylMap_measurableEmbedding c hr T₀)
      (map_restrict_unitCylinder c hr T₀) (ae_mono hμ₀ ha.elliptic)

theorem isParabolicWeakSolution_rescale (a : ParCoeffField d) (c : Vec d) {r : ℝ} (hr : 0 < r)
    (T₀ : ℝ) {I' : Set ℝ} (hI'meas : MeasurableSet I') (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I')
    (u : ParH1Function (euclideanBall c r) I')
    (hu : IsParabolicWeakSolution a (euclideanBall c r) I' u) :
    IsParabolicWeakSolution (fun z => a (cylMap c r T₀ z)) (euclideanBall (0 : Vec d) 1)
      (Ioc (-1 : ℝ) 0) (rescaleParH1 c hr T₀ hI' u) := by
  intro φ
  set φ' := pullbackTest c hr T₀ hI' φ with hφ'
  have hcomp : φ'.toFun ∘ cylMap c r T₀ = φ.toFun := pullbackTest_comp_cylMap c hr T₀ hI' φ
  obtain ⟨hint, hzero⟩ := hu φ'
  have hBm : MeasurableSet (euclideanBall c r) := (isOpen_euclideanBall c r).measurableSet
  have hsub : euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀ ⊆ euclideanBall c r ×ˢ I' :=
    prod_mono subset_rfl hI'
  have hvanish : ∀ w ∈ (euclideanBall c r ×ˢ I') \ (euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀),
      parWeakIntegrand a u φ'.toFun w = 0 := by
    intro w hw
    exact parWeakIntegrand_eq_zero_of_notMem_tsupport a u fun hmem =>
      hw.2 (tsupport_pullbackTest_subset c hr T₀ hI' φ hmem)
  have hint0 : IntegrableOn (parWeakIntegrand a u φ'.toFun)
      (euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀) := hint.mono_set hsub
  have hzero0 : ∫ w in euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀,
      parWeakIntegrand a u φ'.toFun w = 0 := by
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hBm.prod hI'meas) hsub hvanish]
    exact hzero
  have hfun : parWeakIntegrand (fun z => a (cylMap c r T₀ z)) (rescaleParH1 c hr T₀ hI' u)
      φ.toFun = fun z => r ^ 2 * parWeakIntegrand a u φ'.toFun (cylMap c r T₀ z) := by
    funext z
    rw [← hcomp]
    exact parWeakIntegrand_rescale a c hr T₀ hI' u φ'.contDiff z
  have hF := cylMap_measurableEmbedding c hr T₀
  have hmap := map_restrict_unitCylinder c hr T₀
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact (integrable_comp_of_map_eq_smul hF ENNReal.ofReal_ne_top hmap hint0).const_mul _
  · rw [integral_const_mul]
    have := integral_comp_of_map_eq_smul hF hmap (parWeakIntegrand a u φ'.toFun)
    rw [this, hzero0]
    simp

/-- Parabolic rescaling of a weak solution on `B(c, r) × I'` to the unit cylinder
`B₁ × (-1, 0]` via `Φ(y, s) = (c + r • y, T₀ + r ^ 2 * s)`. -/
theorem exists_unit_rescaling {Lam : ℝ} (a : ParCoeffField d) (c : Vec d) {r : ℝ} (hr : 0 < r)
    (T₀ : ℝ) {I' : Set ℝ} (hI'meas : MeasurableSet I') (hI' : Ioc (T₀ - r ^ 2) T₀ ⊆ I')
    (ha : IsParabolicCoeff 1 Lam a (euclideanBall c r) I')
    (u : ParH1Function (euclideanBall c r) I')
    (hu : IsParabolicWeakSolution a (euclideanBall c r) I' u) :
    ∃ (ã : ParCoeffField d)
      (ũ : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)),
      IsParabolicCoeff 1 Lam ã (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) ∧
      IsParabolicWeakSolution ã (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) ũ ∧
      (∀ y s, ũ.toFun (y, s) = u.toFun (c + r • y, T₀ + r ^ 2 * s)) ∧
      ((∀ᵐ w ∂(volume.restrict (euclideanBall c r ×ˢ I')), 0 ≤ u.toFun w) →
        ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
          0 ≤ ũ.toFun z) := by
  refine ⟨fun z => a (cylMap c r T₀ z), rescaleParH1 c hr T₀ hI' u,
    isParabolicCoeff_rescale a c hr T₀ hI' ha,
    isParabolicWeakSolution_rescale a c hr T₀ hI'meas hI' u hu, fun y s => rfl, fun h => ?_⟩
  have hμ₀ : (volume : Measure (Vec d × ℝ)).restrict (euclideanBall c r ×ˢ Ioc (T₀ - r ^ 2) T₀) ≤
      (volume : Measure (Vec d × ℝ)).restrict (euclideanBall c r ×ˢ I') :=
    Measure.restrict_mono (prod_mono subset_rfl hI') le_rfl
  exact ae_comp_of_map_eq_smul (cylMap_measurableEmbedding c hr T₀)
    (map_restrict_unitCylinder c hr T₀) (ae_mono hμ₀ h)

end PDE.Parabolic.Rescale
