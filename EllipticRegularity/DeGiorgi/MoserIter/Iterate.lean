module

public import EllipticRegularity.DeGiorgi.MoserIter.Chain
public import EllipticRegularity.DeGiorgi.MoserIter.EssSup
public import EllipticRegularity.DeGiorgi.MoserIter.Scalar

/-!
# The Moser iteration for subsolutions (abstract form)

From the one-step estimate (4.62) for a function `v` (as a hypothesis `hstep`), the
iteration with `p_n = p₀ γ^n`, `r_n = 1/2 + 2^{-n-2}` gives
`ess sup_{B_{1/2}} v ≤ K ‖v‖_{L^{p₀}(B_{3/4})}` with the explicit constant of the manuscript.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal

namespace PDE.DGNMMoser

/-- The exponent `d/(d-2) > 1`. -/
theorem one_lt_gamma {d : ℕ} (hd : 3 ≤ d) : 1 < (d : ℝ) / (d - 2) := by
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [lt_div_iff₀ (by linarith)]; linarith

/-- The Moser iteration, abstract form. -/
theorem moser_iteration {d : ℕ} (hd : 3 ≤ d) (v : Vec d → ℝ)
    (hv : AEMeasurable v (volumeOn (euclideanBall (0 : Vec d) (1 / 2))))
    {c₁ Λ : ℝ} (hc₁ : 1 ≤ c₁) (hΛ : 1 ≤ Λ)
    (hstep : ∀ p : ℝ, 1 < p → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 3 / 4 →
      eLpNorm v (ENNReal.ofReal (p * ((d : ℝ) / (d - 2))))
          (volumeOn (euclideanBall (0 : Vec d) r)) ≤
        ENNReal.ofReal ((c₁ / (s - r) ^ 2 * (Λ * p ^ 2 / (p - 1) ^ 2 + 1)) ^ (1 / p)) *
          eLpNorm v (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) s)))
    {p₀ : ℝ} (hp₀ : 1 < p₀) :
    essSup (fun x => ENNReal.ofReal (v x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal
          ((128 * c₁ * Λ * (p₀ / (p₀ - 1)) ^ 2) ^ ((d : ℝ) / 2 / p₀) *
            (4 : ℝ) ^ (((d : ℝ) * (d - 2) / 4) / p₀)) *
        eLpNorm v (ENNReal.ofReal p₀) (volumeOn (euclideanBall (0 : Vec d) (3 / 4))) := by
  set γ : ℝ := (d : ℝ) / (d - 2) with hγdef
  have hγ : 1 < γ := one_lt_gamma hd
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  have hT1 : γ / (γ - 1) = (d : ℝ) / 2 := by
    rw [hγdef]; field_simp; ring
  have hT2 : γ / (γ - 1) ^ 2 = (d : ℝ) * (d - 2) / 4 := by
    rw [hγdef]; field_simp; ring
  have hp0pos : 0 < p₀ := by linarith
  have hc0 : 0 < c₁ := by linarith
  have hΛ0 : 0 < Λ := by linarith
  set q : ℝ := p₀ / (p₀ - 1) with hq
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ (by linarith)]; linarith
  set A : ℝ := 128 * c₁ * Λ * q ^ 2 with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    have : 1 ≤ 128 * c₁ * Λ := by nlinarith
    rw [hA]; nlinarith
  set e : ℕ → ℝ := fun n => p₀ * γ ^ n with he
  have he_ge : ∀ n, p₀ ≤ e n := fun n => by
    simp only [he]
    have : 1 ≤ γ ^ n := one_le_pow₀ hγ.le
    nlinarith
  have he_succ : ∀ n, e (n + 1) = e n * γ := fun n => by simp only [he, pow_succ]; ring
  set a : ℕ → ℝ≥0∞ := fun n => eLpNorm v (ENNReal.ofReal (e n))
    (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 4) n))) with ha
  set k : ℕ → ℝ := fun n => (c₁ / (rad (1 / 4) n - rad (1 / 4) (n + 1)) ^ 2 *
    (Λ * e n ^ 2 / (e n - 1) ^ 2 + 1)) ^ (1 / e n) with hk
  have hk0 : ∀ n, 0 ≤ k n := fun n => by
    apply Real.rpow_nonneg
    have : 0 < e n - 1 := by have := he_ge n; linarith
    positivity
  have hkA : ∀ n, k n ≤ (A * 4 ^ n) ^ (e n)⁻¹ := fun n => by
    have hen : 1 < e n := lt_of_lt_of_le hp₀ (he_ge n)
    have hen1 : 0 < e n - 1 := by linarith
    have hinv : c₁ / (rad (1 / 4) n - rad (1 / 4) (n + 1)) ^ 2 = c₁ * (64 * 4 ^ n) := by
      rw [div_eq_mul_one_div, inv_rad_sub_sq (by norm_num)]; ring
    have hq' : e n / (e n - 1) ≤ q := by
      rw [hq, div_le_div_iff₀ hen1 (by linarith)]
      have := he_ge n; nlinarith
    have hq'1 : 1 ≤ e n / (e n - 1) := by rw [le_div_iff₀ hen1]; linarith
    have hX : Λ * e n ^ 2 / (e n - 1) ^ 2 + 1 ≤ 2 * Λ * q ^ 2 := by
      have h1 : Λ * e n ^ 2 / (e n - 1) ^ 2 = Λ * (e n / (e n - 1)) ^ 2 := by
        rw [div_pow]; ring
      have h2 : (e n / (e n - 1)) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by linarith) hq' 2
      have h3 : 1 ≤ (e n / (e n - 1)) ^ 2 := one_le_pow₀ hq'1
      rw [h1]; nlinarith
    simp only [hk]
    rw [hinv, one_div]
    apply Real.rpow_le_rpow
    · have : 0 ≤ Λ * e n ^ 2 / (e n - 1) ^ 2 + 1 := by positivity
      positivity
    · calc c₁ * (64 * 4 ^ n) * (Λ * e n ^ 2 / (e n - 1) ^ 2 + 1)
          ≤ c₁ * (64 * 4 ^ n) * (2 * Λ * q ^ 2) := by gcongr
        _ = A * 4 ^ n := by rw [hA]; ring
    · positivity
  have hprod : ∀ N, ∏ n ∈ range N, k n ≤
      (128 * c₁ * Λ * q ^ 2) ^ ((d : ℝ) / 2 / p₀) * (4 : ℝ) ^ (((d : ℝ) * (d - 2) / 4) / p₀) := by
    intro N
    have h1 := prod_geometric_le hγ hp0pos hA1 (by norm_num : (1 : ℝ) ≤ 4) N
    rw [hT1, hT2] at h1
    exact (Finset.prod_le_prod₀ (fun n _ => hk0 n) fun n _ => hkA n).trans h1
  set K : ℝ := (128 * c₁ * Λ * q ^ 2) ^ ((d : ℝ) / 2 / p₀) *
    (4 : ℝ) ^ (((d : ℝ) * (d - 2) / 4) / p₀) with hK
  have hrad0 : rad (1 / 4) 0 = 3 / 4 := by rw [rad_zero]; norm_num
  have hchain : ∀ N, a N ≤ ENNReal.ofReal K *
      eLpNorm v (ENNReal.ofReal p₀) (volumeOn (euclideanBall (0 : Vec d) (3 / 4))) := by
    intro N
    have hc := chain_le a k hk0 N (fun n _ => by
      have hen : 1 < e n := lt_of_lt_of_le hp₀ (he_ge n)
      have := hstep (e n) hen (rad (1 / 4) (n + 1)) (rad (1 / 4) n)
        (half_le_rad (by norm_num) _) (rad_succ_lt (by norm_num) n)
        (by have := rad_le (c := 1 / 4) (by norm_num) n; linarith)
      simp only [ha, he_succ]
      exact this)
    have ha0 : a 0 = eLpNorm v (ENNReal.ofReal p₀)
        (volumeOn (euclideanBall (0 : Vec d) (3 / 4))) := by
      simp only [ha, he, pow_zero, mul_one, hrad0]
    rw [ha0] at hc
    exact hc.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hprod N)) le_rfl)
  have := isFiniteMeasure_volumeOn_ball d (r := 1 / 2) (by norm_num)
  refine essSup_ofReal_le_of_eLpNorm_le hv (q := e)
    (Filter.Tendsto.const_mul_atTop hp0pos (tendsto_pow_atTop_atTop_of_one_lt hγ)) fun N => ?_
  exact (eLpNorm_ball_mono v _ (by norm_num) (half_le_rad (by norm_num) N)).trans (hchain N)

end PDE.DGNMMoser
