module

public import EllipticRegularity.DeGiorgi.MoserIter.Iterate
public import EllipticRegularity.DeGiorgi.MoserIter.SmallScalar

/-!
# The Moser iteration for small exponents: the geometric case

Step 3, case `p = q γ^{-m}`, of Proposition 4.14, from the one-step estimate
(4.72) (as a hypothesis on the function `f`).
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal

namespace PDE.DGNMMoser

/-- The one-step estimate (4.72), for a function `f`, as consumed by the
iteration. -/
def SmallStep {d : ℕ} (f : Vec d → ℝ) (c₁ Λ : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 →
    eLpNorm f (ENNReal.ofReal (p * ((d : ℝ) / (d - 2))))
        (volumeOn (euclideanBall (0 : Vec d) r)) ≤
      ENNReal.ofReal ((c₁ / (s - r) ^ 2 * (Λ * p ^ 2 / (1 - p) ^ 2 + 1)) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) s))

theorem gamma_sums {d : ℕ} (hd : 3 ≤ d) :
    ((d : ℝ) / (d - 2)) / ((d : ℝ) / (d - 2) - 1) = (d : ℝ) / 2 ∧
    ((d : ℝ) / (d - 2)) / ((d : ℝ) / (d - 2) - 1) ^ 2 = (d : ℝ) * (d - 2) / 4 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  constructor <;> (field_simp; ring)

/-- Geometric case: `p γ^m = q < 1`. -/
theorem small_iteration_geometric {d : ℕ} (hd : 3 ≤ d) {f : Vec d → ℝ}
    {c₁ Λ V : ℝ} (hc₁ : 1 ≤ c₁) (hΛ : 0 ≤ Λ) (hV : 1 ≤ V) (hstep : SmallStep f c₁ Λ)
    {p q : ℝ} (hp : 0 < p) (hq : q < 1) (m : ℕ) (hm : p * ((d : ℝ) / (d - 2)) ^ m = q) :
    eLpNorm f (ENNReal.ofReal (q * ((d : ℝ) / (d - 2))))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal
          ((16 * c₁ * V * (Λ * p ^ 2 / (1 - q) ^ 2 + 1)) ^ ((d : ℝ) / 2 / p) *
            (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p)) *
        eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  set γ : ℝ := (d : ℝ) / (d - 2) with hγdef
  have hγ : 1 < γ := one_lt_gamma hd
  obtain ⟨hT1, hT2⟩ := gamma_sums hd
  have hc0 : 0 < c₁ := by linarith
  set X : ℝ := Λ * p ^ 2 / (1 - q) ^ 2 + 1 with hX
  have hX1 : 1 ≤ X := by rw [hX]; have : 0 ≤ Λ * p ^ 2 / (1 - q) ^ 2 := by positivity
                         linarith
  set A : ℝ := 16 * c₁ * V * X with hA
  have hA1 : 1 ≤ A := by
    rw [hA]
    have h1 : 1 ≤ 16 * c₁ := by linarith
    have h2 : 1 ≤ 16 * c₁ * V := by nlinarith
    nlinarith
  have hB1 : (1 : ℝ) ≤ 4 * γ ^ 2 := by nlinarith
  set e : ℕ → ℝ := fun n => p * γ ^ n with he
  have hepos : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have he_succ : ∀ n, e (n + 1) = e n * γ := fun n => by simp only [he, pow_succ]; ring
  have he_le : ∀ n ≤ m, e n ≤ q := fun n hn => by
    rw [← hm]; simp only [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hγ.le hn) hp.le
  set a : ℕ → ℝ≥0∞ := fun n => eLpNorm f (ENNReal.ofReal (e n))
    (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) n))) with ha
  set k : ℕ → ℝ := fun n => (c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 *
    (Λ * e n ^ 2 / (1 - e n) ^ 2 + 1)) ^ (1 / e n) with hk
  have hk0 : ∀ n, 0 ≤ k n := fun n => by
    apply Real.rpow_nonneg
    have := hepos n
    positivity
  have hkA : ∀ n ∈ range (m + 1), k n ≤ (A * (4 * γ ^ 2) ^ n) ^ (e n)⁻¹ := fun n hn => by
    have hnm : n ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hinv : c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 = c₁ * (16 * 4 ^ n) := by
      rw [div_eq_mul_one_div, inv_rad_sub_sq (by norm_num)]; ring
    have hγn : 1 ≤ (γ ^ 2) ^ n := one_le_pow₀ (by nlinarith)
    have h2 : e n ^ 2 = (γ ^ 2) ^ n * p ^ 2 := by
      simp only [he]; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]; ring
    have hXn := oneStepConst_le hΛ (hepos n) (he_le n hnm) hq h2.le hγn
    simp only [hk]
    rw [hinv]
    exact stepFactor_le hc0.le hV (by linarith) (by have := hepos n; positivity) hXn (hepos n)
  have hprod : ∏ n ∈ range (m + 1), k n ≤
      A ^ ((d : ℝ) / 2 / p) * (4 * γ ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p) := by
    have h1 := prod_geometric_le hγ hp hA1 hB1 (m + 1)
    rw [hT1, hT2] at h1
    exact (Finset.prod_le_prod₀ (fun n _ => hk0 n) hkA).trans h1
  set K : ℝ := A ^ ((d : ℝ) / 2 / p) * (4 * γ ^ 2) ^ (((d : ℝ) * (d - 2) / 4) / p) with hK
  have hrad0 : rad (1 / 2) 0 = 1 := by rw [rad_zero]; norm_num
  have hc := chain_le a k hk0 (m + 1) (fun n hn => by
    have hnm : n ≤ m := Nat.lt_succ_iff.1 hn
    have h1 : e n < 1 := lt_of_le_of_lt (he_le n hnm) hq
    have := hstep (e n) (hepos n) h1 (rad (1 / 2) (n + 1)) (rad (1 / 2) n)
      (half_le_rad (by norm_num) _) (rad_succ_lt (by norm_num) n)
      (by have := rad_le (c := 1 / 2) (by norm_num) n; linarith)
    simp only [ha, he_succ]
    exact this)
  have ha0 : a 0 = eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    simp only [ha, he, pow_zero, mul_one, hrad0]
  rw [ha0] at hc
  have hlast : e (m + 1) = q * γ := by rw [he_succ, ← hm]
  have hmono := eLpNorm_ball_mono f (ENNReal.ofReal (q * γ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (half_le_rad (c := 1 / 2) (by norm_num) (m + 1))
  refine hmono.trans ?_
  have : a (m + 1) = eLpNorm f (ENNReal.ofReal (q * γ))
      (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) (m + 1)))) := by
    simp only [ha, hlast]
  rw [← this]
  exact hc.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hprod) le_rfl)

end PDE.DGNMMoser
