module

public import PDEFoundation.Measure.MatrixPerturbationZeroExtension
public import PDEFoundation.Measure.EuclideanVectorIntegral

/-! # Matrix operator bounds preserved by probability averaging -/

@[expose] public section

namespace PDE
open MeasureTheory

/-- Probability averaging preserves the exact Euclidean operator bound of a
matrix perturbation. Coordinate integrability is derived from the bound. -/
theorem isMatrixPerturbationLE_add_coordinateIntegral_of_probability
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {d : ℕ} (b : α → Mat d) (B : Mat d)
    {delta : ℝ} (_hdelta : 0 ≤ delta)
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) μ)
    (hclose : ∀ᵐ x ∂μ, IsMatrixPerturbationLE delta (b x) (0:Mat d)) :
    IsMatrixPerturbationLE delta
      (B + Matrix.of (fun i j => ∫ x, b x i j ∂μ)) B := by
  have hbint (i j : Fin d) : Integrable (fun x => b x i j) μ := by
    have hmem : MemLp (fun x => b x i j) 1 μ := by
      apply MemLp.of_bound (hb i j).aestronglyMeasurable delta
      filter_upwards [hclose] with x hx
      simpa only [sub_zero, Real.norm_eq_abs] using hx.abs_entry_sub_le i j
    exact hmem.integrable le_rfl
  intro ξ
  let g : α → Vec d := fun x => matVecMul (b x) ξ
  have hgint (i : Fin d) : Integrable (fun x => g x i) μ := by
    dsimp only [g, matVecMul]
    exact integrable_finsetSum _ fun j _ => (hbint i j).mul_const (ξ j)
  have heq : matVecMul ((B + Matrix.of (fun i j => ∫ x, b x i j ∂μ))-B) ξ =
      fun i => ∫ x, g x i ∂μ := by
    classical
    rw [add_sub_cancel_left]
    ext i
    dsimp only [matVecMul, g]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
    · intro j _
      exact (hbint i j).mul_const (ξ j)
  rw [heq]
  calc
    _ ≤ ∫ x, vecEuclideanNorm (g x) ∂μ :=
      vecEuclideanNorm_integral_le_integral_vecEuclideanNorm g hgint
    _ ≤ ∫ _x : α, delta*vecEuclideanNorm ξ ∂μ := by
      apply integral_mono_ae (integrable_vecEuclideanNorm_of_coord g hgint)
        (integrable_const _)
      filter_upwards [hclose] with x hx
      simpa only [g, sub_zero] using hx ξ
    _ = delta*vecEuclideanNorm ξ := by simp

end PDE
