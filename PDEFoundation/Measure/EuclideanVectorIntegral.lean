module

public import PDEFoundation.Ambient.HilbertVec
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Euclidean norm of a native vector integral -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- Coordinatewise integrability of a native finite vector field implies
integrability of its exact Euclidean magnitude. -/
theorem integrable_vecEuclideanNorm_of_coord
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    (g : α → Vec m) (hg : ∀ i, Integrable (fun x => g x i) μ) :
    Integrable (fun x => vecEuclideanNorm (g x)) μ := by
  let G : α → HilbertVec m := fun x => (g x).toHilbertVec
  have hG : Integrable G μ := by
    apply Integrable.of_eval_piLp
    intro i
    simpa only [G, Vec.toHilbertVec_apply] using hg i
  apply hG.norm.congr
  filter_upwards with x
  exact Vec.vecEuclideanNorm_eq_norm_toHilbertVec (g x) |>.symm

/-- The Euclidean norm of the coordinatewise integral of a native vector field
is bounded by the integral of its Euclidean norm. -/
theorem vecEuclideanNorm_integral_le_integral_vecEuclideanNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    (g : α → Vec m) (hg : ∀ i, Integrable (fun x => g x i) μ) :
    vecEuclideanNorm (fun i => ∫ x, g x i ∂μ) ≤
      ∫ x, vecEuclideanNorm (g x) ∂μ := by
  let G : α → HilbertVec m := fun x => (g x).toHilbertVec
  have hG : Integrable G μ := by
    apply Integrable.of_eval_piLp
    intro i
    simpa only [G, Vec.toHilbertVec_apply] using hg i
  have hIntegral :
      Vec.toHilbertVec ((fun i => ∫ x, g x i ∂μ) : Vec m) =
        ∫ x, G x ∂μ := by
    ext i
    rw [MeasureTheory.eval_integral_piLp]
    · rfl
    · intro j
      simpa only [G, Vec.toHilbertVec_apply] using hg j
  rw [Vec.vecEuclideanNorm_eq_norm_toHilbertVec, hIntegral]
  calc
    ‖∫ x, G x ∂μ‖ ≤ ∫ x, ‖G x‖ ∂μ :=
      norm_integral_le_integral_norm G
    _ = ∫ x, vecEuclideanNorm (g x) ∂μ := by
      have hnorm : (fun x => ‖G x‖) =ᵐ[μ]
          fun x => vecEuclideanNorm (g x) := by
        filter_upwards with x
        exact Vec.vecEuclideanNorm_eq_norm_toHilbertVec (g x) |>.symm
      exact integral_congr_ae hnorm

end

end PDE
