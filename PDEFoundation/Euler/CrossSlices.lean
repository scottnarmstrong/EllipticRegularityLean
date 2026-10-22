module

public import PDEFoundation.Euler.CrossDefs

/-!
# Slice hypotheses of the time product rule

Instances of the two time-weak formulations feeding `time_product_identity`: testing the first solution
with the mollified slice of the second (`cross_hU`) and conversely (`cross_hV`, which needs the symmetry of
mollification), together with integrability of the datum forms.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

theorem ae_slice_div_of_weak {T : ℝ} {w : Vec 2 × ℝ → Vec 2} (hw : IsEulerWeakSolution T w) :
    ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, vecDot (w z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0 :=
  hw.2.2.2.1

theorem cross_hU {T : ℝ} (hT : 0 < T) {v₀ : Vec 2 → Vec 2} {u v : Vec 2 × ℝ → Vec 2}
    (hu : IsEulerWeakSolutionWithDatum T v₀ u) (hv : IsEulerWeakSolutionWithDatum T v₀ v)
    {B1 B2 : ℝ} (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      (∃ b, b < T ∧ ∀ τ, b ≤ τ → θ τ = 0) →
      ∫ τ, (deriv θ τ * crossF a u v τ σ + θ τ * crossH a u v τ σ)
        ∂(volume.restrict (Icc (0 : ℝ) T)) + θ 0 * crossD a v₀ v σ = 0 := by
  have h := ae_mollify_slice_div hT hbv.meas hbv.per hbv.bdd (ae_slice_div_of_weak hv.1)
  filter_upwards [h] with σ hσ θ hθ ⟨b, hb, hθb⟩
  obtain ⟨hsm, hper, hdiv, _⟩ := hσ a ha
  exact weak_formulation_product (ζ := mollifyVec a (fun y => v (y, σ))) hu hbu.bdd hsm hper hdiv
    hθ hb hθb

theorem abs_slice_coord_le {w : Vec 2 × ℝ → Vec 2} {t : ℝ} {B : ℝ}
    (hb : ∀ᵐ y ∂(volume : Measure (Vec 2)), vecNormSq (w (y, t)) ≤ B) (i : Fin 2) :
    ∀ᵐ y ∂(volume : Measure (Vec 2)), |w (y, t) i| ≤ Real.sqrt B :=
  hb.mono fun _ hy => abs_coord_le_sqrt hy i

theorem cross_hV {T : ℝ} (hT : 0 < T) {v₀ : Vec 2 → Vec 2} {u v : Vec 2 × ℝ → Vec 2}
    (hu : IsEulerWeakSolutionWithDatum T v₀ u) (hv : IsEulerWeakSolutionWithDatum T v₀ v)
    {B1 B2 : ℝ} (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      (∃ b, b < T ∧ ∀ σ, b ≤ σ → θ σ = 0) →
      ∫ σ, (deriv θ σ * crossF a u v τ σ + θ σ * crossK a u v τ σ)
        ∂(volume.restrict (Icc (0 : ℝ) T)) + θ 0 * crossD a v₀ u τ = 0 := by
  have h := ae_mollify_slice_div hT hbu.meas hbu.per hbu.bdd (ae_slice_div_of_weak hu.1)
  have hlu := ae_slice_locInt hbu.meas hbu.per hbu.bdd
  have hlv := ae_slice_locInt hbv.meas hbv.per hbv.bdd
  filter_upwards [h, hlu] with τ hτ hlτ θ hθ ⟨b, hb, hθb⟩
  obtain ⟨hsm, hper, hdiv, _⟩ := hτ a ha
  have hW := weak_formulation_product (ζ := mollifyVec a (fun y => u (y, τ))) hv hbv.bdd hsm hper hdiv
    hθ hb hθb
  have hsymm : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) T)),
      (∑ i, ∫ x in torusCube, v (x, σ) i * mollifyVec a (fun y => u (y, τ)) x i) =
        crossF a u v τ σ := by
    filter_upwards [hlv] with σ hσ
    unfold crossF
    refine Finset.sum_congr rfl fun i _ => ?_
    have := integral_cube_mollify_mul_comm ha (f := fun y => v (y, σ) i) (g := fun y => u (y, τ) i)
      ((hbv.per σ).comp (fun r => r i)) ((hbu.per τ).comp (fun r => r i)) (hσ.1 i) (hlτ.1 i)
      (Bf := Real.sqrt B2) (Bg := Real.sqrt B1) (abs_slice_coord_le hσ.2 i) (abs_slice_coord_le hlτ.2 i)
    calc ∫ x in torusCube, v (x, σ) i * mollifyVec a (fun y => u (y, τ)) x i
        = ∫ x in torusCube, mollify a (fun y => u (y, τ) i) x * v (x, σ) i := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [mollifyVec_apply]; ring
      _ = ∫ x in torusCube, mollify a (fun y => v (y, σ) i) x * u (x, τ) i := this
      _ = ∫ x in torusCube, u (x, τ) i * mollifyVecST a v (x, σ) i := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [mollifyVecST, mollifyVec_apply]; ring
  have hcongr : ∫ σ, (deriv θ σ * (∑ i, ∫ x in torusCube, v (x, σ) i * mollifyVec a (fun y => u (y, τ)) x i) +
        θ σ * (∑ i, ∑ j, ∫ x in torusCube, (v (x, σ) i * v (x, σ) j) *
          gradMat (mollifyVec a (fun y => u (y, τ))) x i j)) ∂(volume.restrict (Icc (0 : ℝ) T)) =
      ∫ σ, (deriv θ σ * crossF a u v τ σ + θ σ * crossK a u v τ σ) ∂(volume.restrict (Icc (0 : ℝ) T)) := by
    refine integral_congr_ae ?_
    filter_upwards [hsymm] with σ hσ
    simp only [hσ]
    rfl
  rw [← hcongr]
  exact hW

end PDE
