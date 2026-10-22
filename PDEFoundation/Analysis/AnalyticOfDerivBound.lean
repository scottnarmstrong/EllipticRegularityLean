module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Coordinate bounds for higher derivatives

The scalar PDE estimates control iterated derivatives on coordinate vectors.
This file develops the multilinear expansion needed to compare them with
derivatives in arbitrary directions.
-/

@[expose] public section

namespace PDE

/-! ### Coordinate expansion -/

/-- A continuous multilinear map on native vectors expands over the coordinate
vectors, with one factor for each argument. -/
theorem continuousMultilinearMap_apply_eq_sum_coordinates {d m : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ)
    (v : Fin m → Vec d) :
    L v = ∑ ι : Fin m → Fin d,
      (∏ k : Fin m, v k (ι k)) * L (fun k => Pi.single (ι k) 1) := by
  classical
  have hv (k : Fin m) :
      (∑ i : Fin d, (v k i) • Pi.single i (1 : ℝ)) = v k := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  calc
    L v = L (fun k => ∑ i : Fin d, (v k i) • Pi.single i (1 : ℝ)) := by
      congr 1
      funext k
      exact (hv k).symm
    _ = ∑ ι : Fin m → Fin d,
          L (fun k => (v k (ι k)) • Pi.single (ι k) (1 : ℝ)) := by
      exact L.map_sum _
    _ = ∑ ι : Fin m → Fin d,
          (∏ k : Fin m, v k (ι k)) * L (fun k => Pi.single (ι k) 1) := by
      apply Finset.sum_congr rfl
      intro ι _
      rw [L.map_smul_univ]
      rfl

/-- Bounds on all coordinate evaluations control a continuous multilinear map
on arbitrary native vectors through their coordinate one-norms. -/
theorem abs_continuousMultilinearMap_apply_le_coordinate_bound {d m : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ)
    (v : Fin m → Vec d) {B : ℝ}
    (hL : ∀ ι : Fin m → Fin d,
      |L (fun k => Pi.single (ι k) 1)| ≤ B) :
    |L v| ≤ B * ∏ k : Fin m, ∑ i : Fin d, |v k i| := by
  classical
  rw [continuousMultilinearMap_apply_eq_sum_coordinates]
  calc
    |∑ ι : Fin m → Fin d,
        (∏ k : Fin m, v k (ι k)) * L (fun k => Pi.single (ι k) 1)| ≤
        ∑ ι : Fin m → Fin d,
          |(∏ k : Fin m, v k (ι k)) * L (fun k => Pi.single (ι k) 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ι : Fin m → Fin d,
          (∏ k : Fin m, |v k (ι k)|) * B := by
      apply Finset.sum_le_sum
      intro ι _
      rw [abs_mul, Finset.abs_prod]
      exact mul_le_mul_of_nonneg_left (hL ι)
        (Finset.prod_nonneg fun k hk => abs_nonneg _)
    _ = B * ∏ k : Fin m, ∑ i : Fin d, |v k i| := by
      rw [← Finset.sum_mul]
      rw [Fintype.prod_sum]
      ring

/-- For repeated directions, the coordinate factor is the `m`-th power of
the coordinate one-norm. -/
theorem abs_continuousMultilinearMap_diagonal_le_coordinate_bound {d m : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ)
    (h : Vec d) {B : ℝ}
    (hL : ∀ ι : Fin m → Fin d,
      |L (fun k => Pi.single (ι k) 1)| ≤ B) :
    |L (fun _ : Fin m => h)| ≤ B * (∑ i : Fin d, |h i|) ^ m := by
  simpa only [Finset.prod_const, Finset.card_fin, nsmul_eq_mul] using
    abs_continuousMultilinearMap_apply_le_coordinate_bound L (fun _ => h) hL

/-- The operator norm on the inherited supremum norm is bounded by the
largest coordinate evaluation, with the dimension factor `d^m`. -/
theorem norm_continuousMultilinearMap_le_coordinate_bound {d m : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec d) ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ ι : Fin m → Fin d,
      |L (fun k => Pi.single (ι k) 1)| ≤ B) :
    ‖L‖ ≤ B * (d : ℝ) ^ m := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hB (pow_nonneg (Nat.cast_nonneg d) m))
  intro v
  have hv (k : Fin m) :
      (∑ i : Fin d, |v k i|) ≤ (d : ℝ) * ‖v k‖ := by
    simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
      Pi.sum_norm_apply_le_norm (v k)
  have hprod :
      (∏ k : Fin m, ∑ i : Fin d, |v k i|) ≤
        ∏ k : Fin m, (d : ℝ) * ‖v k‖ := by
    exact Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg _)
      (fun k _ => hv k)
  calc
    ‖L v‖ = |L v| := Real.norm_eq_abs _
    _ ≤ B * ∏ k : Fin m, ∑ i : Fin d, |v k i| :=
      abs_continuousMultilinearMap_apply_le_coordinate_bound L v hL
    _ ≤ B * ∏ k : Fin m, (d : ℝ) * ‖v k‖ :=
      mul_le_mul_of_nonneg_left hprod hB
    _ = (B * (d : ℝ) ^ m) * ∏ k : Fin m, ‖v k‖ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_fin]
      ring

/-- Coordinate bounds on an iterated Fréchet derivative imply an operator
norm bound with the explicit dimension factor. -/
theorem norm_iteratedFDeriv_le_of_coordinate_bound {d m : ℕ}
    (f : Vec d → ℝ) (y : Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ ι : Fin m → Fin d,
      |iteratedFDeriv ℝ m f y (fun k => Pi.single (ι k) 1)| ≤ B) :
    ‖iteratedFDeriv ℝ m f y‖ ≤ B * (d : ℝ) ^ m :=
  norm_continuousMultilinearMap_le_coordinate_bound _ hB hderiv

end PDE
