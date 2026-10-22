module

public import PDEFoundation

/-!
# Euclidean geometry for the Harnack chain

A weak triangle inequality for `euclideanSqDist` and the equally spaced points on the segment
between two centres.
-/

@[expose] public section

namespace PDE.Parabolic.NashLower

theorem euclideanSqDist_le_two_mul {d : ℕ} (a b c : Vec d) :
    euclideanSqDist a c ≤ 2 * (euclideanSqDist a b + euclideanSqDist b c) := by
  have hsub : a - c = (2 : ℝ) • ((1 / 2 : ℝ) • (a - b) + (1 / 2 : ℝ) • (b - c)) := by
    ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h := vecNormSq_weighted_add_le (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num) (a - b) (b - c)
  unfold euclideanSqDist
  rw [hsub, vecNormSq_smul]
  linarith

theorem euclideanSqDist_le_four_mul {d : ℕ} (a b c e : Vec d) :
    euclideanSqDist a e ≤
      2 * euclideanSqDist a b + 4 * euclideanSqDist b c + 4 * euclideanSqDist c e := by
  have h1 := euclideanSqDist_le_two_mul a b e
  have h2 := euclideanSqDist_le_two_mul b c e
  linarith

/-- Equally spaced points on the segment from `z` to `x`. -/
noncomputable def pathPt {d : ℕ} (z x : Vec d) (N k : ℕ) : Vec d := z + ((k : ℝ) / N) • (x - z)

theorem pathPt_zero {d : ℕ} (z x : Vec d) (N : ℕ) : pathPt z x N 0 = z := by
  simp [pathPt]

theorem pathPt_self {d : ℕ} (z x : Vec d) {N : ℕ} (hN : N ≠ 0) : pathPt z x N N = x := by
  have : (N : ℝ) / N = 1 := div_self (by exact_mod_cast hN)
  simp [pathPt, this]

theorem euclideanSqDist_pathPt_succ {d : ℕ} (z x : Vec d) {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    euclideanSqDist (pathPt z x N k) (pathPt z x N (k + 1)) =
      (1 / (N : ℝ)) ^ 2 * euclideanSqDist x z := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hsub : pathPt z x N k - pathPt z x N (k + 1) = (-(1 / (N : ℝ))) • (x - z) := by
    ext i
    simp only [pathPt, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  unfold euclideanSqDist
  rw [hsub, vecNormSq_smul]
  ring

end PDE.Parabolic.NashLower
