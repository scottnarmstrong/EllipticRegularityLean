module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Polar coordinates on the native plane `Vec 2`

The parametrization `polarVec ρ θ = (ρ cos θ, ρ sin θ)` of `Vec 2 = Fin 2 → ℝ`
and the polar integration formula
`∫ f = ∫_{ρ > 0} ∫_{-π < θ < π} ρ f(ρ cos θ, ρ sin θ) dθ dρ`
for integrable `f`, together with the integrability of the polar integrand and
of its angular integral. These are transported from Mathlib's `polarCoord` on
`ℝ × ℝ` through the measure-preserving equivalence `Fin 2 → ℝ ≃ ℝ × ℝ`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set

/-- The polar parametrization `(ρ, θ) ↦ (ρ cos θ, ρ sin θ)` of the plane. -/
noncomputable def polarVec (ρ θ : ℝ) : Vec 2 :=
  ![ρ * Real.cos θ, ρ * Real.sin θ]

@[simp]
theorem polarVec_apply_zero (ρ θ : ℝ) : polarVec ρ θ 0 = ρ * Real.cos θ := rfl

@[simp]
theorem polarVec_apply_one (ρ θ : ℝ) : polarVec ρ θ 1 = ρ * Real.sin θ := rfl

/-- The Euclidean squared norm of `polarVec ρ θ` is `ρ²`. -/
theorem vecNormSq_polarVec (ρ θ : ℝ) : vecNormSq (polarVec ρ θ) = ρ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [vecNormSq, vecDot, Fin.sum_univ_two, polarVec_apply_zero, polarVec_apply_one]
  linear_combination ρ ^ 2 * h

/-- `polarVec` is `2π`-periodic in the angle. -/
theorem polarVec_add_two_pi (ρ θ : ℝ) : polarVec ρ (θ + 2 * Real.pi) = polarVec ρ θ := by
  ext i
  fin_cases i <;> simp [polarVec]

private theorem finTwoArrow_symm_polarCoord_symm (p : ℝ × ℝ) :
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (polarCoord.symm p) = polarVec p.1 p.2 := by
  ext i
  fin_cases i <;> rfl

private theorem measurePreserving_finTwoArrow_symm :
    MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure (Vec 2)) :=
  (volume_preserving_finTwoArrow ℝ).symm _

private theorem integrable_comp_finTwoArrow_symm {f : Vec 2 → ℝ} (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ => f ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm p)) := by
  exact (measurePreserving_finTwoArrow_symm.integrable_comp_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.measurableEmbedding).2 hf

/-- The polar integrand `ρ f(polarVec ρ θ)` of an integrable function is
integrable on `(0, ∞) × (-π, π)`. -/
theorem integrableOn_polar {f : Vec 2 → ℝ} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (polarVec p.1 p.2))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  set g : ℝ × ℝ → ℝ := fun p => f ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm p)
  have hg : Integrable g := integrable_comp_finTwoArrow_symm hf
  have himage := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := (volume : Measure (ℝ × ℝ))) (s := polarCoord.target)
    (f := polarCoord.symm) (f' := fderivPolarCoordSymm)
    (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn g).1 hg.integrableOn
  refine himage.congr_fun (fun p hp => ?_) (measurableSet_Ioi.prod measurableSet_Ioo)
  have hp1 : 0 < p.1 := hp.1
  simp only [det_fderivPolarCoordSymm, abs_of_pos hp1, smul_eq_mul, g,
    finTwoArrow_symm_polarCoord_symm]

/-- **Polar integration formula** on `Vec 2`. -/
theorem integral_eq_integral_polar {f : Vec 2 → ℝ} (hf : Integrable f) :
    ∫ x, f x = ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
      ρ * f (polarVec ρ θ) := by
  have h1 : ∫ x, f x =
      ∫ p : ℝ × ℝ, f ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm p) :=
    (measurePreserving_finTwoArrow_symm.integral_comp' (g := f)).symm
  rw [h1, ← integral_comp_polarCoord_symm]
  have h2 : ∫ p in polarCoord.target, p.1 •
        f ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm (polarCoord.symm p)) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, p.1 * f (polarVec p.1 p.2) := by
    simp only [smul_eq_mul, finTwoArrow_symm_polarCoord_symm, polarCoord_target]
  rw [h2]
  exact setIntegral_prod (fun p : ℝ × ℝ => p.1 * f (polarVec p.1 p.2))
    (integrableOn_polar hf)

/-- The angular integral of the polar integrand is integrable in the radius. -/
theorem integrableOn_polar_radial {f : Vec 2 → ℝ} (hf : Integrable f) :
    IntegrableOn (fun ρ => ∫ θ in Ioo (-Real.pi) Real.pi, ρ * f (polarVec ρ θ))
      (Ioi (0 : ℝ)) := by
  have h := integrableOn_polar hf
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact h.integral_prod_left

end PDE.Ch4Spagnolo
