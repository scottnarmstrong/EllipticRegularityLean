module

public import PDEFoundation.Analysis.AnalyticOfDerivBoundLine
public import PDEFoundation.Analysis.AnalyticOfDerivBoundGeometry
public import PDEFoundation.Analysis.AnalyticOfDerivBoundFactorial

/-!
# Quantitative Taylor remainder from coordinate derivative bounds
-/

@[expose] public section

namespace PDE

open scoped Nat

/-- Coordinate derivative bounds give the corresponding bound for ordinary
derivatives along a short affine segment. -/
theorem abs_iteratedDeriv_affine_line_le {d m : ℕ}
    (g : Vec d → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x₀ h : Vec d) {δ M K : ℝ}
    (hδ : 0 < δ) (hh : (∑ i : Fin d, |h i|) < δ)
    (hcoord : ∀ y ∈ euclideanBall x₀ δ,
      ∀ n : ℕ, ∀ ι : Fin n → Fin d,
        |iteratedFDeriv ℝ n g y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * n) ^ n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |iteratedDeriv m (fun s : ℝ => g (x₀ + s • h)) t| ≤
      M * (K * m) ^ m * (∑ i : Fin d, |h i|) ^ m := by
  rw [iteratedDeriv_affine_line g hg x₀ h t]
  exact abs_continuousMultilinearMap_diagonal_le_coordinate_bound _ h
    (hcoord _ (affine_line_mem_euclideanBall_of_sum_abs_lt hδ hh ht) m)

/-- Lagrange's Taylor remainder on a short affine line is bounded by a
geometric term after the factorial estimate. -/
theorem abs_taylor_remainder_affine_line_le_geometric {d : ℕ}
    (g : Vec d → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x₀ h : Vec d) {δ M K : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hh : (∑ i : Fin d, |h i|) < δ)
    (hcoord : ∀ y ∈ euclideanBall x₀ δ,
      ∀ n : ℕ, ∀ ι : Fin n → Fin d,
        |iteratedFDeriv ℝ n g y (fun k => Pi.single (ι k) 1)| ≤
          M * (K * n) ^ n)
    (n : ℕ) :
    |g (x₀ + h) -
        ∑ k ∈ Finset.range (n + 1),
          (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k g x₀ (fun _ => h)| ≤
      M * (Real.exp 1 * K * (∑ i : Fin d, |h i|)) ^ (n + 1) := by
  let γ : ℝ → ℝ := fun t => g (x₀ + t • h)
  have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := by
    exact hg.comp (contDiff_const.add (contDiff_id.smul_const h))
  have hγOn : ContDiffOn ℝ (n + 1) γ (Set.uIcc (0 : ℝ) 1) :=
    hγ.contDiffOn.of_le (by simp)
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := γ) (x := 1) (x₀ := 0) (n := n) (by norm_num) hγOn
  have hpoly :
      taylorWithinEval γ n (Set.uIcc (0 : ℝ) 1) 0 1 =
        ∑ k ∈ Finset.range (n + 1),
          (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k g x₀ (fun _ => h) := by
    rw [taylor_within_apply]
    simp only [sub_zero, one_pow, mul_one, smul_eq_mul, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      (hγ.contDiffAt.of_le (by simp)) (by norm_num)]
    rw [iteratedDeriv_affine_line g hg x₀ h 0]
    simp
  have hξIoo : ξ ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hξ
  have hξIcc : ξ ∈ Set.Icc (0 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self hξIoo
  have hderiv := abs_iteratedDeriv_affine_line_le g hg x₀ h hδ hh hcoord hξIcc
    (m := n + 1)
  have hfact : (0 : ℝ) < ((n + 1) ! : ℝ) := by positivity
  have hsum : 0 ≤ ∑ i : Fin d, |h i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [hpoly] at hrem
  simp only [γ, one_smul] at hrem
  rw [hrem]
  simp only [sub_zero, one_pow, mul_one, abs_div, abs_of_pos hfact]
  calc
    |iteratedDeriv (n + 1) γ ξ| / ((n + 1) ! : ℝ) ≤
        (M * (K * (n + 1)) ^ (n + 1) * (∑ i : Fin d, |h i|) ^ (n + 1)) /
          ((n + 1) ! : ℝ) :=
      div_le_div_of_nonneg_right
        (by simpa only [Nat.cast_add, Nat.cast_one] using hderiv) hfact.le
    _ ≤ M * (Real.exp 1 * K * (∑ i : Fin d, |h i|)) ^ (n + 1) :=
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        scaled_pow_line_div_factorial_le_geometric (n + 1) hM hK hsum)

end PDE
