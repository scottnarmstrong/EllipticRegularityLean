module

public import PDEFoundation.Measure.DyadicSparseSum
public import PDEFoundation.Geometry.DyadicBoxAtPoint

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

/-- At a fixed point, a finite family of containing literal dyadic descendants
has geometric depth sum at most two. -/
theorem sum_half_pow_length_le_two_of_mem
    {d : ℕ} (I : Box (Fin d)) (x : Vec d)
    (T : Finset (List (Set (Fin d))))
    (hT : ∀ q ∈ T, x ∈ (dyadicDescendant I q : Set (Vec d))) :
    (∑ q ∈ T, (1 / 2 : ℝ) ^ q.length) ≤ 2 := by
  classical
  have hinj : Set.InjOn List.length (↑T : Set (List (Set (Fin d)))) := by
    intro p hp q hq hpq
    by_contra hne
    exact (Set.disjoint_left.mp
      (disjoint_dyadicDescendant_of_length_eq I hpq hne)) (hT p hp) (hT q hq)
  have hsum : (∑ q ∈ T, (1 / 2 : ℝ) ^ q.length) =
      ∑ n ∈ T.image List.length, (1 / 2 : ℝ) ^ n := by
    exact (Finset.sum_image hinj).symm
  rw [hsum]
  have hle := (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum
      (T.image List.length) (fun n _ => pow_nonneg (by norm_num) n)
  calc
    (∑ n ∈ T.image List.length, (1 / 2 : ℝ) ^ n) ≤
        ∑' n : ℕ, (1 / 2 : ℝ) ^ n := hle
    _ = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)]
      norm_num

/-- Geometric depth energy is summed pointwise, with coefficient two and no
exponent-dependent loss, on any subfamily of literal dyadic descendants. -/
theorem dyadicSparseSum_geometric_le_two
    {d : ℕ} (I : Box (Fin d)) (S : Set (List (Set (Fin d))))
    {A : ℝ} (hA : 0 ≤ A) (x : Vec d) :
    dyadicSparseSum I S (fun q => A * (1 / 2 : ℝ) ^ q.length) x ≤
      ENNReal.ofReal (2 * A) := by
  classical
  rw [dyadicSparseSum_eq_iSup_finiteSparseSum I S _
    (fun q _ => mul_nonneg hA (pow_nonneg (by norm_num) _)) x]
  apply iSup_le
  intro T
  let U := finsetWithinSet T S
  let V := U.filter (fun q => x ∈ (dyadicDescendant I q : Set (Vec d)))
  have hsum : finiteSparseSum I U (fun q => A * (1 / 2 : ℝ) ^ q.length) x =
      A * ∑ q ∈ V, (1 / 2 : ℝ) ^ q.length := by
    unfold finiteSparseSum V
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hx : x ∈ (dyadicDescendant I q : Set (Vec d))
    · simp only [hx, indicator_of_mem, ite_true]
    · simp only [hx, ite_false, mul_zero]
      exact Set.indicator_of_notMem hx (fun _ : Vec d => A * (1 / 2 : ℝ) ^ q.length)
  have hV : ∀ q ∈ V, x ∈ (dyadicDescendant I q : Set (Vec d)) := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  rw [hsum]
  apply ENNReal.ofReal_le_ofReal
  calc
    A * ∑ q ∈ V, (1 / 2 : ℝ) ^ q.length ≤ A * 2 :=
      mul_le_mul_of_nonneg_left (sum_half_pow_length_le_two_of_mem I x V hV) hA
    _ = 2 * A := mul_comm _ _

/-- A geometric energy bound and sparse source coefficients split before any
Lp norm is taken. -/
theorem dyadicSparseSum_le_geometric_add
    {d : ℕ} (I : Box (Fin d)) (S : Set (List (Set (Fin d))))
    (a b : List (Set (Fin d)) → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ q ∈ S, 0 ≤ b q)
    (hab : ∀ q ∈ S, a q ≤ A * (1 / 2 : ℝ) ^ q.length + B * b q)
    (x : Vec d) :
    dyadicSparseSum I S a x ≤
      ENNReal.ofReal (2 * A) + ENNReal.ofReal B * dyadicSparseSum I S b x := by
  classical
  have hsum : dyadicSparseSum I S a x ≤
      dyadicSparseSum I S (fun q => A * (1 / 2 : ℝ) ^ q.length) x +
        ENNReal.ofReal B * dyadicSparseSum I S b x := by
    unfold dyadicSparseSum
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro q
    by_cases hq : q ∈ S
    · simp only [Set.indicator_of_mem hq]
      by_cases hx : x ∈ (dyadicDescendant I q : Set (Vec d))
      · simp only [Set.indicator_of_mem hx]
        have h := ENNReal.ofReal_le_ofReal (hab q hq)
        rwa [ENNReal.ofReal_add
          (mul_nonneg hA (pow_nonneg (by norm_num) _)) (mul_nonneg hB (hb q hq)),
          ENNReal.ofReal_mul hB] at h
      · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero, mul_zero,
          add_zero, le_refl]
    · simp only [Set.indicator_of_notMem hq, mul_zero, add_zero, le_refl]
  exact hsum.trans (add_le_add (dyadicSparseSum_geometric_le_two I S hA x) le_rfl)

end PDE
