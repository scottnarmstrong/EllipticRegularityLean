module

public import EllipticRegularity.Guerra.Scalar.Function

/-!
# Guerra sharpness: the Hölder seminorm bound `[u]_{C^{0,α}} ≤ 5γ`

Proved directly (without gradients): for `|y| ≤ |x|` either `|x-y| ≥ |y|` and one uses
`|u| ≤ |·|^α`, or one splits `u(x)-u(y) = (|x|^α-|y|^α)φ(t_x) + |y|^α(φ(t_x)-φ(t_y))`.
-/

@[expose] public section

namespace PDE.Guerra

open Real PDE

variable {d : ℕ}

private theorem norm_sub_le' (x y : Vec d) :
    vecEuclideanNorm x ≤ vecEuclideanNorm y + vecEuclideanNorm (x - y) := by
  have := vecEuclideanNorm_add_le y (x - y)
  simpa using this

private theorem coord_ratio_diff (i : Fin d) {x y : Vec d} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : vecEuclideanNorm y ≤ vecEuclideanNorm x) :
    |x i / vecEuclideanNorm x - y i / vecEuclideanNorm y| ≤
      2 * vecEuclideanNorm (x - y) / vecEuclideanNorm y := by
  have hrx := vecEuclideanNorm_pos_of_ne hx
  have hry := vecEuclideanNorm_pos_of_ne hy
  set δ := vecEuclideanNorm (x - y)
  have h1 : |x i - y i| ≤ δ := abs_apply_le_vecEuclideanNorm (x - y) i
  have h2 : |vecEuclideanNorm x - vecEuclideanNorm y| ≤ δ := by
    rw [abs_le]
    have a := norm_sub_le' x y
    have b := norm_sub_le' y x
    rw [vecEuclideanNorm_sub_comm y x] at b
    constructor <;> linarith
  have h3 : |x i| ≤ vecEuclideanNorm x := abs_apply_le_vecEuclideanNorm x i
  have e : x i / vecEuclideanNorm x - y i / vecEuclideanNorm y =
      (x i - y i) / vecEuclideanNorm y +
        x i * (vecEuclideanNorm y - vecEuclideanNorm x) /
          (vecEuclideanNorm x * vecEuclideanNorm y) := by
    field_simp
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(x i - y i) / vecEuclideanNorm y| ≤ δ / vecEuclideanNorm y := by
    rw [abs_div, abs_of_pos hry]; exact div_le_div_of_nonneg_right h1 hry.le
  have t2 : |x i * (vecEuclideanNorm y - vecEuclideanNorm x) /
      (vecEuclideanNorm x * vecEuclideanNorm y)| ≤ δ / vecEuclideanNorm y := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hrx hry), abs_sub_comm, div_le_div_iff₀
      (mul_pos hrx hry) hry]
    have : |x i| * |vecEuclideanNorm x - vecEuclideanNorm y| ≤ vecEuclideanNorm x * δ :=
      mul_le_mul h3 h2 (abs_nonneg _) hrx.le
    nlinarith [mul_pos hrx hry]
  have : 2 * δ / vecEuclideanNorm y = δ / vecEuclideanNorm y + δ / vecEuclideanNorm y := by ring
  linarith

private theorem holder_aux (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (hα1 : α ≤ 1)
    {x y : Vec d} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : vecEuclideanNorm y ≤ vecEuclideanNorm x) :
    |uProf i γ α x - uProf i γ α y| ≤ 5 * γ * vecEuclideanNorm (x - y) ^ α := by
  have hrx := vecEuclideanNorm_pos_of_ne hx
  have hry := vecEuclideanNorm_pos_of_ne hy
  have hγ0 : 0 < γ := by linarith
  set δ := vecEuclideanNorm (x - y) with hδ
  have hδ0 : 0 ≤ δ := vecEuclideanNorm_nonneg _
  have hδα : 0 ≤ δ ^ α := Real.rpow_nonneg hδ0 α
  have hux := abs_uProf_le i hγ hα x
  have huy := abs_uProf_le i hγ hα y
  have hrxle : vecEuclideanNorm x ≤ vecEuclideanNorm y + δ := norm_sub_le' x y
  by_cases hc : vecEuclideanNorm y ≤ δ
  · -- far case
    have h1 : vecEuclideanNorm x ^ α ≤ (2 * δ) ^ α :=
      Real.rpow_le_rpow hrx.le (by linarith) hα.le
    have h2 : vecEuclideanNorm y ^ α ≤ δ ^ α := Real.rpow_le_rpow hry.le hc hα.le
    have h3 : (2 * δ) ^ α = 2 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ0
    have h4 : (2 : ℝ) ^ α ≤ 2 := by
      calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
        _ = 2 := Real.rpow_one 2
    calc |uProf i γ α x - uProf i γ α y| ≤ |uProf i γ α x| + |uProf i γ α y| := abs_sub _ _
      _ ≤ 2 * δ ^ α + δ ^ α := by
          have : (2 * δ) ^ α ≤ 2 * δ ^ α := by rw [h3]; exact mul_le_mul_of_nonneg_right h4 hδα
          linarith
      _ ≤ 5 * γ * δ ^ α := by nlinarith
  · -- near case
    push Not at hc
    rw [uProf_eq_of_ne i γ α hx, uProf_eq_of_ne i γ α hy]
    set tx := x i / vecEuclideanNorm x
    set ty := y i / vecEuclideanNorm y
    have htx : |phi γ tx| ≤ 1 := by
      apply abs_phi_le_one hγ
      rw [abs_div, abs_of_pos hrx, div_le_one hrx]
      exact abs_apply_le_vecEuclideanNorm x i
    have hrr : vecEuclideanNorm y ^ α ≤ vecEuclideanNorm x ^ α :=
      Real.rpow_le_rpow hry.le hxy hα.le
    have hsub : vecEuclideanNorm x ^ α - vecEuclideanNorm y ^ α ≤ δ ^ α := by
      have := Real.rpow_add_le_add_rpow (a := vecEuclideanNorm x - vecEuclideanNorm y)
        (b := vecEuclideanNorm y) (by linarith) hry.le hα.le hα1
      have h5 : (vecEuclideanNorm x - vecEuclideanNorm y) ^ α ≤ δ ^ α :=
        Real.rpow_le_rpow (by linarith) (by linarith) hα.le
      simp only [sub_add_cancel] at this
      linarith
    have hfirst : |(vecEuclideanNorm x ^ α - vecEuclideanNorm y ^ α) * phi γ tx| ≤ δ ^ α := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      nlinarith [abs_nonneg (phi γ tx), sub_nonneg.2 hrr]
    -- second term
    have hphi := abs_phi_sub_le hγ tx ty
    have hcoord := coord_ratio_diff i hx hy hxy
    have hq : δ / vecEuclideanNorm y ≤ (δ / vecEuclideanNorm y) ^ α := by
      have h0 : 0 ≤ δ / vecEuclideanNorm y := div_nonneg hδ0 hry.le
      have h1 : δ / vecEuclideanNorm y ≤ 1 := (div_le_one hry).2 hc.le
      have := Real.rpow_le_rpow_of_exponent_ge' h0 h1 hα.le hα1
      simpa using this
    have hkey : vecEuclideanNorm y ^ α * (δ / vecEuclideanNorm y) ≤ δ ^ α := by
      calc vecEuclideanNorm y ^ α * (δ / vecEuclideanNorm y)
          ≤ vecEuclideanNorm y ^ α * (δ / vecEuclideanNorm y) ^ α :=
            mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hry.le α)
        _ = (vecEuclideanNorm y * (δ / vecEuclideanNorm y)) ^ α :=
            (Real.mul_rpow hry.le (div_nonneg hδ0 hry.le)).symm
        _ = δ ^ α := by rw [mul_div_cancel₀ _ hry.ne']
    have hsecond : |vecEuclideanNorm y ^ α * (phi γ tx - phi γ ty)| ≤ 4 * γ * δ ^ α := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hry.le α)]
      have h6 : |phi γ tx - phi γ ty| ≤ 2 * γ * (2 * (δ / vecEuclideanNorm y)) := by
        refine hphi.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
        have : 2 * δ / vecEuclideanNorm y = 2 * (δ / vecEuclideanNorm y) := by ring
        linarith
      calc vecEuclideanNorm y ^ α * |phi γ tx - phi γ ty|
          ≤ vecEuclideanNorm y ^ α * (2 * γ * (2 * (δ / vecEuclideanNorm y))) :=
            mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hry.le α)
        _ = 4 * γ * (vecEuclideanNorm y ^ α * (δ / vecEuclideanNorm y)) := by ring
        _ ≤ 4 * γ * δ ^ α := mul_le_mul_of_nonneg_left hkey (by linarith)
    have e : vecEuclideanNorm x ^ α * phi γ tx - vecEuclideanNorm y ^ α * phi γ ty =
        (vecEuclideanNorm x ^ α - vecEuclideanNorm y ^ α) * phi γ tx +
          vecEuclideanNorm y ^ α * (phi γ tx - phi γ ty) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith

/-- The Euclidean Hölder seminorm bound `[u]_{C^{0,α}} ≤ 5γ` on the whole space. -/
theorem uProf_holder_univ (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (hα1 : α ≤ 1) :
    EuclideanHolderSeminormLE (Set.univ : Set (Vec d)) (uProf i γ α) α (5 * γ) := by
  intro x _ y _
  have hγ0 : 0 < γ := by linarith
  by_cases hx : x = 0
  · subst hx
    rw [uProf_zero, zero_sub, abs_neg]
    refine (abs_uProf_le i hγ hα y).trans ?_
    rw [zero_sub, vecEuclideanNorm_neg]
    have := Real.rpow_nonneg (vecEuclideanNorm_nonneg y) α
    nlinarith
  by_cases hy : y = 0
  · subst hy
    rw [uProf_zero, sub_zero, sub_zero]
    refine (abs_uProf_le i hγ hα x).trans ?_
    have := Real.rpow_nonneg (vecEuclideanNorm_nonneg x) α
    nlinarith
  rcases le_total (vecEuclideanNorm y) (vecEuclideanNorm x) with h | h
  · exact holder_aux i hγ hα hα1 hx hy h
  · have := holder_aux i hγ hα hα1 hy hx h
    rwa [abs_sub_comm, vecEuclideanNorm_sub_comm y x] at this

/-- The Hölder bound on `B_1` (or on any subset). -/
theorem uProf_holder (i : Fin d) {γ α : ℝ} (hγ : 1 ≤ γ) (hα : 0 < α) (hα1 : α ≤ 1)
    (U : Set (Vec d)) : EuclideanHolderSeminormLE U (uProf i γ α) α (5 * γ) :=
  fun x _ y _ => uProf_holder_univ i hγ hα hα1 x (Set.mem_univ _) y (Set.mem_univ _)

end PDE.Guerra
