module

public import PDEFoundation.Analysis.AnalyticOfDerivBound

/-!
# Round-ball control for affine Taylor lines
-/

@[expose] public section

namespace PDE

/-- The coordinate one-norm is controlled by the inherited supremum norm. -/
theorem sum_abs_coordinates_le_card_mul_norm {d : ℕ} (h : Vec d) :
    (∑ i : Fin d, |h i|) ≤ (d : ℝ) * ‖h‖ := by
  simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    Pi.sum_norm_apply_le_norm h

/-- A short affine segment remains in the explicit round ball. -/
theorem affine_line_mem_euclideanBall_of_sum_abs_lt {d : ℕ}
    {x₀ h : Vec d} {δ t : ℝ} (hδ : 0 < δ)
    (hh : (∑ i : Fin d, |h i|) < δ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x₀ + t • h ∈ euclideanBall x₀ δ := by
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).2
  have hsub : (x₀ + t • h) - x₀ = t • h := by abel
  rw [hsub, vecEuclideanNorm_smul]
  have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  calc
    |t| * vecEuclideanNorm h ≤ 1 * vecEuclideanNorm h :=
      mul_le_mul_of_nonneg_right ht_abs (by unfold vecEuclideanNorm; positivity)
    _ = vecEuclideanNorm h := one_mul _
    _ ≤ ∑ i : Fin d, |h i| := vecEuclideanNorm_le_sum_abs h
    _ < δ := hh

end PDE
