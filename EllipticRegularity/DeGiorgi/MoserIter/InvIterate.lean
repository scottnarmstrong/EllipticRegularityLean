module

public import EllipticRegularity.DeGiorgi.MoserIter.Iterate

/-!
# The Moser iteration for reciprocals of supersolutions (abstract form)

From the one-step estimate (4.71) for a function `g` (the reciprocal of a
positive supersolution), the iteration with `p_n = p₀ γ^n`, `r_n = (1 + 2^{-n})/2` gives
`ess sup_{B_{1/2}} g ≤ K ‖g‖_{L^{p₀}(B_1)}`.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal

namespace PDE.DGNMMoser

/-- The Moser iteration to `p → ∞` for the reciprocal of a supersolution. -/
theorem inv_moser_iteration {d : ℕ} (hd : 3 ≤ d) (g : Vec d → ℝ)
    (hg : AEMeasurable g (volumeOn (euclideanBall (0 : Vec d) (1 / 2))))
    {c₁ Λ : ℝ} (hc₁ : 1 ≤ c₁) (hΛ : 0 ≤ Λ)
    (hstep : ∀ p : ℝ, 0 < p → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 →
      eLpNorm g (ENNReal.ofReal (p * ((d : ℝ) / (d - 2))))
          (volumeOn (euclideanBall (0 : Vec d) r)) ≤
        ENNReal.ofReal ((c₁ / (s - r) ^ 2 * (Λ * p ^ 2 / (1 + p) ^ 2 + 1)) ^ (1 / p)) *
          eLpNorm g (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) s)))
    {p₀ : ℝ} (hp₀ : 0 < p₀) :
    essSup (fun x => ENNReal.ofReal (g x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal
          ((16 * c₁ * (Λ * p₀ ^ 2 + 1)) ^ ((d : ℝ) / 2 / p₀) *
            (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p₀)) *
        eLpNorm g (ENNReal.ofReal p₀) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  set γ : ℝ := (d : ℝ) / (d - 2) with hγdef
  have hγ : 1 < γ := one_lt_gamma hd
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  have hT1 : γ / (γ - 1) = (d : ℝ) / 2 := by
    rw [hγdef]; field_simp; ring
  have hT2 : γ / (γ - 1) ^ 2 = (d : ℝ) * (d - 2) / 4 := by
    rw [hγdef]; field_simp; ring
  have hc0 : 0 < c₁ := by linarith
  set Z : ℝ := Λ * p₀ ^ 2 + 1 with hZ
  have hZ1 : 1 ≤ Z := by rw [hZ]; nlinarith [sq_nonneg p₀, mul_nonneg hΛ (sq_nonneg p₀)]
  set A : ℝ := 16 * c₁ * Z with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  have hB1 : (1 : ℝ) ≤ 4 * γ ^ 2 := by nlinarith
  set e : ℕ → ℝ := fun n => p₀ * γ ^ n with he
  have hepos : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have he_succ : ∀ n, e (n + 1) = e n * γ := fun n => by simp only [he, pow_succ]; ring
  set a : ℕ → ℝ≥0∞ := fun n => eLpNorm g (ENNReal.ofReal (e n))
    (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) n))) with ha
  set k : ℕ → ℝ := fun n => (c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 *
    (Λ * e n ^ 2 / (1 + e n) ^ 2 + 1)) ^ (1 / e n) with hk
  have hk0 : ∀ n, 0 ≤ k n := fun n => by
    apply Real.rpow_nonneg
    have := hepos n
    positivity
  have hkA : ∀ n, k n ≤ (A * (4 * γ ^ 2) ^ n) ^ (e n)⁻¹ := fun n => by
    have hen := hepos n
    have hinv : c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 = c₁ * (16 * 4 ^ n) := by
      rw [div_eq_mul_one_div, inv_rad_sub_sq (by norm_num)]; ring
    have hγn : 1 ≤ (γ ^ 2) ^ n := one_le_pow₀ (by nlinarith)
    have hX : Λ * e n ^ 2 / (1 + e n) ^ 2 + 1 ≤ (γ ^ 2) ^ n * Z := by
      have h1 : Λ * e n ^ 2 / (1 + e n) ^ 2 ≤ Λ * e n ^ 2 := by
        apply div_le_self (by positivity)
        nlinarith
      have h2 : e n ^ 2 = p₀ ^ 2 * (γ ^ 2) ^ n := by
        simp only [he]; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
      rw [hZ]
      nlinarith
    simp only [hk]
    rw [hinv, one_div]
    apply Real.rpow_le_rpow
    · positivity
    · calc c₁ * (16 * 4 ^ n) * (Λ * e n ^ 2 / (1 + e n) ^ 2 + 1)
          ≤ c₁ * (16 * 4 ^ n) * ((γ ^ 2) ^ n * Z) := by gcongr
        _ = A * (4 * γ ^ 2) ^ n := by rw [hA, mul_pow]; ring
    · positivity
  have hprod : ∀ N, ∏ n ∈ range N, k n ≤
      A ^ ((d : ℝ) / 2 / p₀) * (4 * γ ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p₀) := by
    intro N
    have h1 := prod_geometric_le hγ hp₀ hA1 hB1 N
    rw [hT1, hT2] at h1
    exact (Finset.prod_le_prod₀ (fun n _ => hk0 n) fun n _ => hkA n).trans h1
  set K : ℝ := A ^ ((d : ℝ) / 2 / p₀) * (4 * γ ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p₀) with hK
  have hrad0 : rad (1 / 2) 0 = 1 := by rw [rad_zero]; norm_num
  have hchain : ∀ N, a N ≤ ENNReal.ofReal K *
      eLpNorm g (ENNReal.ofReal p₀) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    intro N
    have hc := chain_le a k hk0 N (fun n _ => by
      have := hstep (e n) (hepos n) (rad (1 / 2) (n + 1)) (rad (1 / 2) n)
        (half_le_rad (by norm_num) _) (rad_succ_lt (by norm_num) n)
        (by have := rad_le (c := 1 / 2) (by norm_num) n; linarith)
      simp only [ha, he_succ]
      exact this)
    have ha0 : a 0 = eLpNorm g (ENNReal.ofReal p₀)
        (volumeOn (euclideanBall (0 : Vec d) 1)) := by
      simp only [ha, he, pow_zero, mul_one, hrad0]
    rw [ha0] at hc
    exact hc.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hprod N)) le_rfl)
  have := isFiniteMeasure_volumeOn_ball d (r := 1 / 2) (by norm_num)
  refine essSup_ofReal_le_of_eLpNorm_le hg (q := e)
    (Filter.Tendsto.const_mul_atTop hp₀ (tendsto_pow_atTop_atTop_of_one_lt hγ)) fun N => ?_
  exact (eLpNorm_ball_mono g _ (by norm_num) (half_le_rad (by norm_num) N)).trans (hchain N)

end PDE.DGNMMoser
