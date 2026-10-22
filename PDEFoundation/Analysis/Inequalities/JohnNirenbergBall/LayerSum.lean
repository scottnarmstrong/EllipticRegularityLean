module

public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Level
public import PDEFoundation.Analysis.Inequalities.JohnNirenbergBall.Series

/-!
# Summation over the cubes of a layer

The cubes of `layerUnion k` are pairwise disjoint, so a per-cube bound of the form
`∫_Q g ≤ c |Q|` (or `|Q ∩ S| ≤ c |Q|`) sums to the same bound for `layerUnion k`.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open BoxIntegral MeasureTheory Set PDE.JohnNirenberg
open scoped ENNReal

variable {d : ℕ} {R : ℝ} {x : Vec d} (hd : 0 < d) (hR : 0 < R) (k : ℕ)

theorem pairwiseDisjoint_layerCubes :
    Pairwise (Function.onFun Disjoint fun n : {n : Fin d → ℤ // IsLayerIndex hd hR x k n} =>
      (gridCube hd hR k n.1 : Set (Vec d))) := by
  intro n m hnm
  exact disjoint_boxGrid (gridSide_pos hd hR k) (fun h => hnm (Subtype.ext h))

theorem volume_layerUnion_eq_tsum :
    volume (layerUnion hd hR x k) =
      ∑' n : {n : Fin d → ℤ // IsLayerIndex hd hR x k n},
        volume (gridCube hd hR k n.1 : Set (Vec d)) :=
  measure_iUnion (pairwiseDisjoint_layerCubes hd hR k) fun _ => Box.measurableSet_coe _

theorem volume_layerUnion_ne_top : volume (layerUnion hd hR x k) ≠ ∞ := by
  refine ne_top_of_le_ne_top (volume_euclideanBall_ne_top x hR.le) (measure_mono ?_)
  intro z hz
  exact (layerUnion_subset hd hR k hz).1

/-- Per-cube integral bounds sum over the layer. -/
theorem lintegral_layerUnion_le (g : Vec d → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ n : Fin d → ℤ, IsLayerIndex hd hR x k n →
      ∫⁻ z in (gridCube hd hR k n : Set (Vec d)), g z ≤ c * volume (gridCube hd hR k n : Set (Vec d))) :
    ∫⁻ z in layerUnion hd hR x k, g z ≤ c * volume (layerUnion hd hR x k) := by
  refine (lintegral_iUnion_le
    (fun n : {n : Fin d → ℤ // IsLayerIndex hd hR x k n} =>
      (gridCube hd hR k n.1 : Set (Vec d))) g).trans ?_
  rw [volume_layerUnion_eq_tsum hd hR k, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => h n.1 n.2

/-- Per-cube measure bounds sum over the layer. -/
theorem measure_layerUnion_inter_le (P : Vec d → Prop) (c : ℝ≥0∞)
    (h : ∀ n : Fin d → ℤ, IsLayerIndex hd hR x k n →
      volume {z ∈ (gridCube hd hR k n : Set (Vec d)) | P z} ≤
        c * volume (gridCube hd hR k n : Set (Vec d))) :
    volume {z ∈ layerUnion hd hR x k | P z} ≤ c * volume (layerUnion hd hR x k) := by
  have hsub : {z ∈ layerUnion hd hR x k | P z} ⊆
      ⋃ n : {n : Fin d → ℤ // IsLayerIndex hd hR x k n},
        {z ∈ (gridCube hd hR k n.1 : Set (Vec d)) | P z} := by
    rintro z ⟨hz, hPz⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨n, hn, hPz⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  rw [volume_layerUnion_eq_tsum hd hR k, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => h n.1 n.2

/-- `|layerUnion k| ≤ 2 d 2⁻ᵏ |B|` in `ℝ≥0∞`. -/
theorem volume_layerUnion_le_ofReal :
    volume (layerUnion hd hR x k) ≤
      ENNReal.ofReal (2 * d / 2 ^ k) * volume (euclideanBall x R) := by
  have hBtop := volume_euclideanBall_ne_top x hR.le
  have h := volume_layerUnion_le (x := x) hd hR k
  calc volume (layerUnion hd hR x k)
      = ENNReal.ofReal (volume (layerUnion hd hR x k)).toReal :=
        (ENNReal.ofReal_toReal (volume_layerUnion_ne_top hd hR k)).symm
    _ ≤ ENNReal.ofReal (2 * d / 2 ^ k * (volume (euclideanBall x R)).toReal) :=
        ENNReal.ofReal_le_ofReal h
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hBtop]

end PDE.JohnNirenbergBall
