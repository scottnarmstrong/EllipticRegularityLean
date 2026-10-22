module

public import PDEFoundation.Analysis.Newtonian.Potential.KernelBounds

/-!
# Lipschitz estimate for the Newton kernel away from the origin

`|E_i(a - v) - E_i(a)| ≤ c_d (1 + 2d) |v| (|a|/2)^{-d}` whenever `2|v| ≤ |a|`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem zpow_neg_natCast_le {m x : ℝ} (k : ℕ) (hm : 0 < m) (hx : m ≤ x) :
    x ^ (-(k : ℤ)) ≤ m ^ (-(k : ℤ)) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos hm k) (pow_le_pow_left₀ hm.le hx k)

/-- Mean value estimate for `t ↦ t^{-d}` on `[m, ∞)`. -/
theorem abs_zpow_neg_sub_le (d : ℕ) {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |x ^ (-(d : ℤ)) - y ^ (-(d : ℤ))| ≤ d * m ^ (-(d : ℤ) - 1) * |x - y| := by
  have hderiv : ∀ t ∈ Ici m, HasDerivAt (fun s : ℝ => s ^ (-(d : ℤ)))
      (((-(d : ℤ) : ℤ) : ℝ) * t ^ (-(d : ℤ) - 1)) t := fun t ht =>
    hasDerivAt_zpow (-(d : ℤ)) t (Or.inl (hm.trans_le ht).ne')
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun s : ℝ => s ^ (-(d : ℤ)))
    (C := d * m ^ (-(d : ℤ) - 1)) (s := Ici m)
    (fun t ht => (hderiv t ht).differentiableAt)
    (fun t ht => by
      rw [(hderiv t ht).deriv, Real.norm_eq_abs, abs_mul]
      have h1 : |(((-(d : ℤ) : ℤ) : ℝ))| = d := by simp
      rw [h1, abs_of_pos (zpow_pos (hm.trans_le ht) _)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
      have := zpow_neg_natCast_le (d + 1) hm ht
      have e : -(d : ℤ) - 1 = -((d + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [e])
    (convex_Ici m) hy hx
  simpa only [Real.norm_eq_abs] using hb

theorem abs_newtonKernel_apply_sub_le (i : Fin d) {a v : Vec d}
    (ha : 0 < vecEuclideanNorm a) (hv : 2 * vecEuclideanNorm v ≤ vecEuclideanNorm a) :
    |newtonKernel (a - v) i - newtonKernel a i| ≤
      newtonConst d * (1 + 2 * d) * vecEuclideanNorm v *
        (vecEuclideanNorm a / 2) ^ (-(d : ℤ)) := by
  set m : ℝ := vecEuclideanNorm a / 2 with hmdef
  have hm : 0 < m := by rw [hmdef]; linarith
  have hnv0 := vecEuclideanNorm_nonneg v
  have hnvm : vecEuclideanNorm v ≤ m := by rw [hmdef]; linarith
  have h1 : vecEuclideanNorm a ≤ vecEuclideanNorm (a - v) + vecEuclideanNorm v := by
    have := vecEuclideanNorm_add_le (a - v) v
    rwa [sub_add_cancel] at this
  have h2 : vecEuclideanNorm (a - v) ≤ vecEuclideanNorm a + vecEuclideanNorm v := by
    have := vecEuclideanNorm_add_le a (-v)
    rwa [← sub_eq_add_neg, vecEuclideanNorm_neg] at this
  have hzm : m ≤ vecEuclideanNorm (a - v) := by rw [hmdef] at hnvm ⊢; linarith
  have ham : m ≤ vecEuclideanNorm a := by rw [hmdef]; linarith
  set g : Vec d → ℝ := fun z => vecEuclideanNorm z ^ (-(d : ℤ)) with hg
  have hker : ∀ z : Vec d, newtonKernel z i = newtonConst d * (g z * z i) := by
    intro z
    rw [newtonKernel_eq]
    simp only [Pi.smul_apply, smul_eq_mul, hg]
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    ring
  have hdiff : newtonKernel (a - v) i - newtonKernel a i =
      newtonConst d * (-(v i) * g (a - v) + a i * (g (a - v) - g a)) := by
    rw [hker, hker]
    simp only [Pi.sub_apply]
    ring
  have hgz : g (a - v) ≤ m ^ (-(d : ℤ)) := zpow_neg_natCast_le d hm hzm
  have hgz0 : 0 ≤ g (a - v) := zpow_nonneg (vecEuclideanNorm_nonneg _) _
  have hdg : |g (a - v) - g a| ≤ d * m ^ (-(d : ℤ) - 1) * vecEuclideanNorm v := by
    refine (abs_zpow_neg_sub_le d hm hzm ham).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_le]
    constructor <;> linarith
  have hvi : |v i| ≤ vecEuclideanNorm v := abs_apply_le_vecEuclideanNorm v i
  have hai : |a i| ≤ 2 * m := by
    have := abs_apply_le_vecEuclideanNorm a i
    rw [hmdef]; linarith
  have hmp : m * m ^ (-(d : ℤ) - 1) = m ^ (-(d : ℤ)) := by
    rw [← zpow_one_add₀ hm.ne']
    congr 1
    ring
  have hmz : 0 < m ^ (-(d : ℤ)) := zpow_pos hm _
  have hmz1 : 0 < m ^ (-(d : ℤ) - 1) := zpow_pos hm _
  rw [hdiff, abs_mul, abs_of_nonneg newtonConst_nonneg]
  have hin : |-(v i) * g (a - v) + a i * (g (a - v) - g a)| ≤
      (1 + 2 * d) * vecEuclideanNorm v * m ^ (-(d : ℤ)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hgz0]
    have t1 : |v i| * g (a - v) ≤ vecEuclideanNorm v * m ^ (-(d : ℤ)) :=
      mul_le_mul hvi hgz hgz0 hnv0
    have t2 : |a i| * |g (a - v) - g a| ≤
        2 * m * (d * m ^ (-(d : ℤ) - 1) * vecEuclideanNorm v) :=
      mul_le_mul hai hdg (abs_nonneg _) (by positivity)
    have t3 : 2 * m * (d * m ^ (-(d : ℤ) - 1) * vecEuclideanNorm v) =
        2 * d * vecEuclideanNorm v * m ^ (-(d : ℤ)) := by
      rw [← hmp]; ring
    nlinarith [t1, t2, t3]
  calc newtonConst d * |-(v i) * g (a - v) + a i * (g (a - v) - g a)|
      ≤ newtonConst d * ((1 + 2 * d) * vecEuclideanNorm v * m ^ (-(d : ℤ))) :=
        mul_le_mul_of_nonneg_left hin newtonConst_nonneg
    _ = _ := by ring

end

end PDE
