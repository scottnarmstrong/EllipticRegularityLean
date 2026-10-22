module

public import PDEFoundation.Geometry.SquareShell
public import PDEFoundation.Sobolev.Cutoff.Ball

/-!
# A quantitative smooth cutoff for dyadic square shells

The canonical radial cutoff is reindexed onto a closed inner square and an
open outer square. In dimension two the inner square of half-side `r` lies
strictly inside the Euclidean ball of radius `3r/2`, while the Euclidean ball
of radius `2r` lies in the outer square of half-side `2r`.
-/

@[expose] public section

namespace PDE

theorem closedCenteredAxisCube_subset_euclideanBall_three_halves
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    closedCenteredAxisCube x₀ r ⊆ euclideanBall x₀ (3 * r / 2) := by
  intro x hx
  have hx0 := hx 0 (Set.mem_univ 0)
  have hx1 := hx 1 (Set.mem_univ 1)
  change x₀ 0 - r ≤ x 0 ∧ x 0 ≤ x₀ 0 + r at hx0
  change x₀ 1 - r ≤ x 1 ∧ x 1 ≤ x₀ 1 + r at hx1
  have h0abs : |x 0 - x₀ 0| ≤ r := by
    rw [abs_le]
    constructor <;> linarith [hx0.1, hx0.2]
  have h1abs : |x 1 - x₀ 1| ≤ r := by
    rw [abs_le]
    constructor <;> linarith [hx1.1, hx1.2]
  have h0sq : (x 0 - x₀ 0) ^ 2 ≤ r ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos hr] using h0abs
  have h1sq : (x 1 - x₀ 1) ^ 2 ≤ r ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos hr] using h1abs
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
  have hnormsq :
      vecEuclideanNorm (x - x₀) ^ 2 =
        (x 0 - x₀ 0) ^ 2 + (x 1 - x₀ 1) ^ 2 := by
    rw [vecEuclideanNorm_sq, vecNormSq_eq_sum_sq]
    simp only [Fin.sum_univ_two, Pi.sub_apply]
  have hnormnonneg : 0 ≤ vecEuclideanNorm (x - x₀) :=
    vecEuclideanNorm_nonneg _
  nlinarith

theorem euclideanBall_two_mul_subset_centeredAxisCube
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ (2 * r) ⊆ centeredAxisCube x₀ (2 * r) := by
  intro x hx
  have hnorm : vecEuclideanNorm (x - x₀) < 2 * r :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  intro i _
  have habs : |(x - x₀) i| ≤ vecEuclideanNorm (x - x₀) :=
    abs_apply_le_vecEuclideanNorm _ i
  have hcoord : |x i - x₀ i| < 2 * r := by
    simpa only [Pi.sub_apply] using lt_of_le_of_lt habs hnorm
  change x₀ i - 2 * r < x i ∧ x i < x₀ i + 2 * r
  rw [abs_lt] at hcoord
  constructor <;> linarith [hcoord.1, hcoord.2]

/-- A smooth cutoff equal to one on the closed square of half-side `r`,
supported in the open square of half-side `2r`, with explicit Euclidean
gradient bound `64 / r`. -/
noncomputable def quantitativeSquareShellCutoff
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r) :
    QuantitativeSmoothCutoff
      (closedCenteredAxisCube x₀ r)
      (centeredAxisCube x₀ (2 * r))
      (64 / r) := by
  let η := quantitativeBallCutoff x₀ (r := 3 * r / 2) (R := 2 * r)
    (by positivity) (by linarith)
  have hinner :
      closedCenteredAxisCube x₀ r ⊆ euclideanBall x₀ (3 * r / 2) :=
    closedCenteredAxisCube_subset_euclideanBall_three_halves x₀ hr
  have houter :
      euclideanBall x₀ (2 * r) ⊆ centeredAxisCube x₀ (2 * r) :=
    euclideanBall_two_mul_subset_centeredAxisCube x₀ hr
  convert η.reindex hinner houter using 1
  field_simp [hr.ne']
  ring

end PDE
