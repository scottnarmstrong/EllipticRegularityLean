module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.CubeChain
public import PDEFoundation.Geometry.BoxGrid

/-!
# Grid cubes at boundary-distance scales (Step 3 of Proposition 1.17)

`layerSet x R k` is the boundary layer `A_k = {R 2^{-k-1} ≤ s ≤ R 2^{-k}}`, where
`s(z) = R - |z - x|`. `gridCube k n` is the cube of the grid `ℓ_k ℤ^d`, `ℓ_k = R 2^{-k} / (4 √d)`,
with index `n`. `layerUnion k` is the union of the grid cubes meeting `A_k`.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {R : ℝ} {x : Vec d}

/-- The side length `ℓ_k = R 2⁻ᵏ / (4 √d)` of the grid cubes at scale `k`. -/
noncomputable def gridSide (d : ℕ) (R : ℝ) (k : ℕ) : ℝ := R / 2 ^ k / (4 * Real.sqrt d)

theorem gridSide_pos (hd : 0 < d) (hR : 0 < R) (k : ℕ) : 0 < gridSide d R k := by
  have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  unfold gridSide; positivity

theorem sqrt_mul_gridSide_div_two (hd : 0 < d) (k : ℕ) :
    Real.sqrt d * gridSide d R k / 2 = R / 2 ^ k / 8 := by
  have : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)).ne'
  unfold gridSide; field_simp; ring

/-- The grid cube of scale `k` and index `n`. -/
noncomputable def gridCube (hd : 0 < d) (hR : 0 < R) (k : ℕ) (n : Fin d → ℤ) : Box (Fin d) :=
  boxGrid (gridSide d R k) (gridSide_pos hd hR k) n

/-- The boundary layer `A_k`. -/
def layerSet (x : Vec d) (R : ℝ) (k : ℕ) : Set (Vec d) :=
  {z | R / 2 ^ (k + 1) ≤ R - vecEuclideanNorm (z - x) ∧
    R - vecEuclideanNorm (z - x) ≤ R / 2 ^ k}

/-- The grid cube `n` meets the layer `A_k`. -/
def IsLayerIndex (hd : 0 < d) (hR : 0 < R) (x : Vec d) (k : ℕ) (n : Fin d → ℤ) : Prop :=
  ∃ z ∈ (gridCube hd hR k n : Set (Vec d)), z ∈ layerSet x R k

/-- The union of the grid cubes of scale `k` meeting the layer `A_k`. -/
def layerUnion (hd : 0 < d) (hR : 0 < R) (x : Vec d) (k : ℕ) : Set (Vec d) :=
  ⋃ n : {n : Fin d → ℤ // IsLayerIndex hd hR x k n}, (gridCube hd hR k n.1 : Set (Vec d))

theorem gridCube_width (hd : 0 < d) (hR : 0 < R) (k : ℕ) (n : Fin d → ℤ) (i : Fin d) :
    (gridCube hd hR k n).upper i - (gridCube hd hR k n).lower i = gridSide d R k :=
  upper_sub_lower_boxGrid _ _ _ _

theorem norm_sub_boxCenter_le_of_mem (hd : 0 < d) (hR : 0 < R) (k : ℕ) (n : Fin d → ℤ)
    {z : Vec d} (hz : z ∈ (gridCube hd hR k n : Set (Vec d))) :
    vecEuclideanNorm (z - boxCenter (gridCube hd hR k n)) ≤ R / 2 ^ k / 8 := by
  have := vecEuclideanNorm_sub_boxCenter_le (gridCube hd hR k n) (gridSide d R k) hd
    (gridCube_width hd hR k n) hz
  rwa [sqrt_mul_gridSide_div_two hd k] at this

/-- The boundary distance of the center of a layer cube. -/
theorem layerIndex_center_bounds (hd : 0 < d) (hR : 0 < R) {k : ℕ} {n : Fin d → ℤ}
    (hn : IsLayerIndex hd hR x k n) :
    3 / 8 * (R / 2 ^ k) ≤ R - vecEuclideanNorm (boxCenter (gridCube hd hR k n) - x) ∧
      R - vecEuclideanNorm (boxCenter (gridCube hd hR k n) - x) ≤ 9 / 8 * (R / 2 ^ k) := by
  obtain ⟨z, hzQ, hz1, hz2⟩ := hn
  have hzc := norm_sub_boxCenter_le_of_mem hd hR k n hzQ
  set c := boxCenter (gridCube hd hR k n)
  have h1 : vecEuclideanNorm (c - x) ≤ vecEuclideanNorm (z - x) + vecEuclideanNorm (z - c) := by
    calc vecEuclideanNorm (c - x) = vecEuclideanNorm ((z - x) + (c - z)) := by congr 1; abel
      _ ≤ vecEuclideanNorm (z - x) + vecEuclideanNorm (c - z) := vecEuclideanNorm_add_le _ _
      _ = _ := by rw [vecEuclideanNorm_sub_comm c z]
  have h2 : vecEuclideanNorm (z - x) ≤ vecEuclideanNorm (c - x) + vecEuclideanNorm (z - c) := by
    calc vecEuclideanNorm (z - x) = vecEuclideanNorm ((c - x) + (z - c)) := by congr 1; abel
      _ ≤ _ := vecEuclideanNorm_add_le _ _
  have hp : 0 < R / 2 ^ k := by positivity
  have hp2 : R / 2 ^ (k + 1) = R / 2 ^ k / 2 := by rw [pow_succ]; field_simp
  constructor <;> linarith

/-- A layer cube lies in `B_R(x)`. -/
theorem gridCube_subset_ball (hd : 0 < d) (hR : 0 < R) {k : ℕ} {n : Fin d → ℤ}
    (hn : IsLayerIndex hd hR x k n) : (gridCube hd hR k n : Set (Vec d)) ⊆ euclideanBall x R :=
  (Box.coe_subset_euclideanClosedBall_boxCenter _ _ hd (gridCube_width hd hR k n)).trans
    (by
      rw [sqrt_mul_gridSide_div_two hd k]
      exact closedBall_subset_of_boundaryLayer hR k (layerIndex_center_bounds hd hR hn).1)

/-- Points of a layer cube have boundary distance at most `5/4 · R 2⁻ᵏ`. -/
theorem boundaryDist_le_of_mem_gridCube (hd : 0 < d) (hR : 0 < R) {k : ℕ} {n : Fin d → ℤ}
    (hn : IsLayerIndex hd hR x k n) {z : Vec d} (hz : z ∈ (gridCube hd hR k n : Set (Vec d))) :
    R - vecEuclideanNorm (z - x) ≤ 5 / 4 * (R / 2 ^ k) := by
  have hzc := norm_sub_boxCenter_le_of_mem hd hR k n hz
  have hc := (layerIndex_center_bounds hd hR hn).2
  set c := boxCenter (gridCube hd hR k n)
  have h1 : vecEuclideanNorm (c - x) ≤ vecEuclideanNorm (z - x) + vecEuclideanNorm (z - c) := by
    calc vecEuclideanNorm (c - x) = vecEuclideanNorm ((z - x) + (c - z)) := by congr 1; abel
      _ ≤ vecEuclideanNorm (z - x) + vecEuclideanNorm (c - z) := vecEuclideanNorm_add_le _ _
      _ = _ := by rw [vecEuclideanNorm_sub_comm c z]
  have hp : 0 < R / 2 ^ k := by positivity
  linarith

theorem layerUnion_subset (hd : 0 < d) (hR : 0 < R) (k : ℕ) :
    layerUnion hd hR x k ⊆ {z ∈ euclideanBall x R |
      R - vecEuclideanNorm (z - x) ≤ 5 / 4 * (R / 2 ^ k)} := by
  intro z hz
  obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hz
  exact ⟨gridCube_subset_ball hd hR n.2 hzn, boundaryDist_le_of_mem_gridCube hd hR n.2 hzn⟩

/-- Every point of the ball lies in some boundary layer. -/
theorem exists_mem_layerSet (hR : 0 < R) {z : Vec d} (hz : z ∈ euclideanBall x R) :
    ∃ k : ℕ, z ∈ layerSet x R k := by
  have hzn := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hz
  set s := R - vecEuclideanNorm (z - x) with hs
  have hspos : 0 < s := by rw [hs]; linarith
  have hsR : s ≤ R := by rw [hs]; linarith [vecEuclideanNorm_nonneg (z - x)]
  have h1 : s / R ≤ 1 := (div_le_one hR).mpr hsR
  have h0 : 0 < s / R := by positivity
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one h0 h1 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  refine ⟨k, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hk1.le hR.le
    rw [div_mul_cancel₀ _ hR.ne'] at h
    rw [← hs]
    calc R / 2 ^ (k + 1) = (1 / 2) ^ (k + 1) * R := by rw [one_div_pow]; ring
      _ ≤ s := h
  · have h := mul_le_mul_of_nonneg_right hk2 hR.le
    rw [div_mul_cancel₀ _ hR.ne'] at h
    rw [← hs]
    calc s ≤ (1 / 2) ^ k * R := h
      _ = R / 2 ^ k := by rw [one_div_pow]; ring

theorem ball_subset_iUnion_layerUnion (hd : 0 < d) (hR : 0 < R) :
    euclideanBall x R ⊆ ⋃ k : ℕ, layerUnion hd hR x k := by
  intro z hz
  obtain ⟨k, hk⟩ := exists_mem_layerSet hR hz
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  refine Set.mem_iUnion.mpr ⟨⟨boxGridIndex (gridSide d R k) z, ?_⟩, ?_⟩
  · exact ⟨z, mem_boxGrid_index (gridSide_pos hd hR k) z, hk⟩
  · exact mem_boxGrid_index (gridSide_pos hd hR k) z

end PDE.JohnNirenbergBall
