module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Regularity.FieldHolder
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Hölder bounds for smooth native fields -/

@[expose] public section

namespace PDE

noncomputable section

private theorem exists_euclideanHolderSeminormLE_half_of_contDiff
    {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ K : ℝ, 0 ≤ K ∧
      EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) 1) f (1 / 2) K := by
  let S := euclideanClosedBall (0 : Vec d) 1
  have hdf : Continuous (fun x => fderiv ℝ f x) :=
    hf.continuous_fderiv (by norm_num)
  obtain ⟨L, hL⟩ :=
    (isCompact_euclideanClosedBall (0 : Vec d) (R := 1) (by norm_num)).exists_bound_of_continuousOn
      hdf.continuousOn
  let K := 2 * max L 0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro x hx y hy
  have hxS : x ∈ S := euclideanBall_subset_euclideanClosedBall _ _ hx
  have hyS : y ∈ S := euclideanBall_subset_euclideanClosedBall _ _ hy
  have hlip : |f x - f y| ≤ max L 0 * ‖x - y‖ := by
    have h := (convex_euclideanClosedBall (0 : Vec d) 1).norm_image_sub_le_of_norm_fderiv_le
      (C := max L (0 : ℝ))
      (fun z _ => (hf.differentiable (by simp) z))
      (fun z hz => (hL z hz).trans (le_max_left L 0))
      hxS hyS
    simpa only [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] using h
  have hxy : vecEuclideanNorm (x - y) < 2 := by
    have hx0 := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    have hy0 := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hy
    calc
      vecEuclideanNorm (x - y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
        simpa only [sub_eq_add_neg, vecEuclideanNorm_neg] using
          vecEuclideanNorm_add_le x (-y)
      _ < 2 := by
        simp only [sub_zero] at hx0 hy0
        linarith
  have hsqrt : vecEuclideanNorm (x - y) ≤
      2 * Real.sqrt (vecEuclideanNorm (x - y)) := by
    have hn := vecEuclideanNorm_nonneg (x - y)
    have hs := Real.sq_sqrt hn
    have hsr := Real.sqrt_nonneg (vecEuclideanNorm (x - y))
    nlinarith
  calc
    |f x - f y| ≤ max L 0 * ‖x - y‖ := hlip
    _ ≤ max L 0 * vecEuclideanNorm (x - y) :=
      mul_le_mul_of_nonneg_left (norm_le_vecEuclideanNorm _) (le_max_right _ _)
    _ ≤ max L 0 * (2 * Real.sqrt (vecEuclideanNorm (x - y))) :=
      mul_le_mul_of_nonneg_left hsqrt (le_max_right _ _)
    _ = K * vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      dsimp [K]
      ring

/-- A componentwise smooth native vector field has a finite Euclidean
one-half-Hölder seminorm on the unit ball. -/
theorem exists_euclideanFieldHolderSeminormLE_half_of_contDiff
    {d k : ℕ} {F : Vec d → Vec k}
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x i)) :
    ∃ K : ℝ, 0 ≤ K ∧
      EuclideanFieldHolderSeminormLE
        (euclideanBall (0 : Vec d) 1) F (1 / 2) K := by
  choose K hK hholder using fun i =>
    exists_euclideanHolderSeminormLE_half_of_contDiff (hF i)
  let L := ∑ i : Fin k, K i
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => hK i
  refine ⟨(k : ℝ) * L, mul_nonneg (Nat.cast_nonneg _) hL, ?_⟩
  apply euclideanFieldHolderSeminormLE_of_coordinates
  intro i
  exact (hholder i).mono_const (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i))

/-- A componentwise smooth native matrix field has a finite Euclidean
operator one-half-Hölder seminorm on the unit ball. -/
theorem exists_euclideanMatrixHolderSeminormLE_half_of_contDiff
    {d : ℕ} {a : CoeffField d}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j)) :
    ∃ K : ℝ, 0 ≤ K ∧
      EuclideanMatrixHolderSeminormLE
        (euclideanBall (0 : Vec d) 1) a (1 / 2) K := by
  choose K hK hholder using fun i j =>
    exists_euclideanHolderSeminormLE_half_of_contDiff (ha i j)
  let L := ∑ i : Fin d, ∑ j : Fin d, K i j
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => hK i j
  refine ⟨(d : ℝ) * (d : ℝ) * L,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hL, ?_⟩
  intro x hx y hy ξ
  have hentry (i j : Fin d) :
      |(a x - a y) i j| ≤ L * vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ) := by
    have hij : K i j ≤ L := by
      have hrow : K i j ≤ ∑ j : Fin d, K i j :=
        Finset.single_le_sum (fun j _ => hK i j) (Finset.mem_univ j)
      have htotal : (∑ j : Fin d, K i j) ≤ L :=
        Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg fun j _ => hK i j) (Finset.mem_univ i)
      exact hrow.trans htotal
    exact (hholder i j x hx y hy).trans (mul_le_mul_of_nonneg_right hij
      (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _))
  calc
    vecEuclideanNorm (matVecMul (a x - a y) ξ) ≤
        ∑ i : Fin d, |matVecMul (a x - a y) ξ i| :=
      vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin d,
        (d : ℝ) *
          (L * vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ) * vecEuclideanNorm ξ) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |matVecMul (a x - a y) ξ i| ≤
            ∑ j : Fin d, |(a x - a y) i j| * |ξ j| := by
          unfold matVecMul
          exact (Finset.abs_sum_le_sum_abs _ _).trans_eq
            (Finset.sum_congr rfl fun j _ => abs_mul _ _)
        _ ≤ ∑ _j : Fin d,
            L * vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ) *
              vecEuclideanNorm ξ := by
          exact Finset.sum_le_sum fun j _ =>
            mul_le_mul (hentry i j) (abs_apply_le_vecEuclideanNorm ξ j)
              (abs_nonneg _) (mul_nonneg hL
                (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _))
        _ = (d : ℝ) *
            (L * vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ) *
              vecEuclideanNorm ξ) := by simp
    _ = ((d : ℝ) * (d : ℝ) * L * vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ)) *
        vecEuclideanNorm ξ := by simp [Finset.sum_const]; ring

end

end PDE
