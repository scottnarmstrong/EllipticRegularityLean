module

public import PDEFoundation.Analysis.ModulusRadius
public import PDEFoundation.Regularity.FieldHolder
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-! # Uniform coefficient freezing from a prescribed modulus -/

@[expose] public section

namespace PDE

open Filter
open scoped Topology

variable {d : ℕ}

/-- The freezing radius is chosen before the domain, coefficient field and
center. Thus it is uniform over all fields with the prescribed modulus. -/
theorem exists_uniform_matrix_oscillation_radius
    {ω : ℝ → ℝ} (hω0 : ω 0 = 0)
    (hωlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ∀ (U : Set (Vec d)) (a : CoeffField d),
        (∀ x ∈ U, ∀ y ∈ U,
          IsMatrixPerturbationLE (ω (vecEuclideanNorm (x - y))) (a x) (a y)) →
        ∀ z : Vec d, euclideanBall z r ⊆ U →
          ∀ x ∈ euclideanBall z r, ∀ y ∈ euclideanBall z r,
            IsMatrixPerturbationLE δ (a x) (a y) := by
  obtain ⟨r, hr, hrle, hsmall⟩ := exists_small_modulus_radius hω0 hωlim hδ
  refine ⟨r, hr, hrle, ?_⟩
  intro U a hmod z hball x hx y hy ξ
  have hxnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hx
  have hynorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy
  have hdist : vecEuclideanNorm (x - y) ≤ 2 * r := by
    have hsum : x - y = (x - z) + (z - y) := by abel
    calc
      vecEuclideanNorm (x - y) = vecEuclideanNorm ((x - z) + (z - y)) := by rw [hsum]
      _ ≤ vecEuclideanNorm (x - z) + vecEuclideanNorm (z - y) :=
        vecEuclideanNorm_add_le _ _
      _ = vecEuclideanNorm (x - z) + vecEuclideanNorm (y - z) := by
        rw [vecEuclideanNorm_sub_comm z y]
      _ ≤ 2 * r := by linarith only [hxnorm, hynorm]
  exact (hmod x (hball hx) y (hball hy) ξ).trans
    (mul_le_mul_of_nonneg_right
      (hsmall _ (vecEuclideanNorm_nonneg _) hdist) (vecEuclideanNorm_nonneg ξ))

end PDE
