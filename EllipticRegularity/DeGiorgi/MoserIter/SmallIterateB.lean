module

public import EllipticRegularity.DeGiorgi.MoserIter.SmallIterate
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The Moser iteration for small exponents: the shifted case

Step 3, case `p < p'`, of Proposition 4.14: a first step from `p` to `p' < γ p` combining
the one-step estimate with Holder's inequality, followed by the geometric iteration
`p' γ^n`.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal

namespace PDE.DGNMMoser

/-- Shifted case: `p ≤ p' ≤ γ p`, `p' γ^m = q < 1`. -/
theorem small_iteration_shifted {d : ℕ} (hd : 3 ≤ d) {f : Vec d → ℝ}
    (hf : AEMeasurable f (volumeOn (euclideanBall (0 : Vec d) 1)))
    {c₁ Λ V : ℝ} (hc₁ : 1 ≤ c₁) (hΛ : 0 ≤ Λ) (hV : 1 ≤ V)
    (hVol : volume (euclideanBall (0 : Vec d) 1) ≤ ENNReal.ofReal V)
    (hstep : SmallStep f c₁ Λ) {p p' q : ℝ} (hp : 0 < p) (hpp' : p ≤ p')
    (hp'γ : p' ≤ p * ((d : ℝ) / (d - 2))) (hq : q < 1) (m : ℕ)
    (hm : p' * ((d : ℝ) / (d - 2)) ^ m = q) :
    eLpNorm f (ENNReal.ofReal (q * ((d : ℝ) / (d - 2))))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal
          ((16 * c₁ * V * (Λ * p ^ 2 / (1 - q) ^ 2 + 1)) ^ ((1 + (d : ℝ) / 2) / p) *
            (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ (((d : ℝ) / 2 + (d : ℝ) * (d - 2) / 4) / p)) *
        eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  set γ : ℝ := (d : ℝ) / (d - 2) with hγdef
  have hγ : 1 < γ := one_lt_gamma hd
  obtain ⟨hT1, hT2⟩ := gamma_sums hd
  have hc0 : 0 < c₁ := by linarith
  have hp'0 : 0 < p' := lt_of_lt_of_le hp hpp'
  have hV0 : 0 < V := by linarith
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
  have hγ0 : 0 < γ := by linarith
  set e : ℕ → ℝ := fun n => if n = 0 then p else p' * γ ^ (n - 1) with he
  have he0 : e 0 = p := by simp [he]
  have he1 : e 1 = p' := by simp [he]
  have hepos : ∀ n, 0 < e n := fun n => by
    simp only [he]; split_ifs
    · exact hp
    · positivity
  have he_succ : ∀ n, 1 ≤ n → e (n + 1) = e n * γ := fun n hn => by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp only [he, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]
    rw [pow_succ]; ring
  have hqp' : p' ≤ q := by
    rw [← hm]
    calc p' = p' * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ hγ.le) hp'0.le
  have he_le : ∀ n, n ≤ m + 1 → e n ≤ q := fun n hn => by
    by_cases h0 : n = 0
    · subst h0; rw [he0]; exact hpp'.trans hqp'
    · simp only [he, h0, ite_false]
      rw [← hm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hγ.le (by omega)) hp'0.le
  have he_sq : ∀ n, 1 ≤ n → e n ^ 2 ≤ (γ ^ 2) ^ n * p ^ 2 := fun n hn => by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h1 : e (j + 1) ≤ p * γ ^ (j + 1) := by
      simp only [he, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
      rw [pow_succ, ← mul_assoc, mul_comm p, mul_assoc]
      calc p' * γ ^ j ≤ (p * γ) * γ ^ j := by gcongr
        _ = _ := by ring
    have h2 : e (j + 1) ^ 2 ≤ (p * γ ^ (j + 1)) ^ 2 :=
      pow_le_pow_left₀ (hepos _).le h1 2
    calc _ ≤ _ := h2
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (j + 1)]; ring
  have hfin1 := isFiniteMeasure_volumeOn_ball d (r := rad (1 / 2 : ℝ) 1) (by
    have := half_le_rad (c := (1 / 2 : ℝ)) (by norm_num) 1; linarith)
  set a : ℕ → ℝ≥0∞ := fun n => eLpNorm f (ENNReal.ofReal (e n))
    (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) n))) with ha
  set k : ℕ → ℝ := fun n => (if n = 0 then V ^ (1 / p) else 1) *
    (c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 *
      (Λ * e n ^ 2 / (1 - e n) ^ 2 + 1)) ^ (1 / e n) with hk
  have hk0 : ∀ n, 0 ≤ k n := fun n => by
    apply mul_nonneg
    · split_ifs
      · positivity
      · norm_num
    · apply Real.rpow_nonneg
      have := hepos n
      positivity
  have hkA : ∀ n ∈ range (m + 1 + 1), k n ≤ (A * (4 * γ ^ 2) ^ n) ^ (e n)⁻¹ := fun n hn => by
    have hnm : n ≤ m + 1 := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hinv : c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 = c₁ * (16 * 4 ^ n) := by
      rw [div_eq_mul_one_div, inv_rad_sub_sq (by norm_num)]; ring
    have hγn : 1 ≤ (γ ^ 2) ^ n := one_le_pow₀ (by nlinarith)
    have hsq : e n ^ 2 ≤ (γ ^ 2) ^ n * p ^ 2 := by
      by_cases h0 : n = 0
      · subst h0; simp [he0]
      · exact he_sq n (by omega)
    have hXn := oneStepConst_le hΛ (hepos n) (he_le n hnm) hq hsq hγn
    simp only [hk]
    rw [hinv]
    by_cases h0 : n = 0
    · subst h0
      simp only [ite_true, he0, pow_zero, mul_one]
      rw [← Real.mul_rpow hV0.le (by have := hepos 0; rw [he0] at this; positivity)]
      rw [inv_eq_one_div]
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      have hXn' : Λ * p ^ 2 / (1 - p) ^ 2 + 1 ≤ X := by
        have := hXn; simp only [he0, pow_zero, one_mul] at this; exact this
      calc V * (c₁ * 16 * (Λ * p ^ 2 / (1 - p) ^ 2 + 1)) ≤ V * (c₁ * 16 * X) := by gcongr
        _ = A := by rw [hA]; ring
    · simp only [h0, ite_false, one_mul]
      exact stepFactor_le hc0.le hV (by linarith) (by have := hepos n; positivity) hXn
        (hepos n)
  have hprod : ∏ n ∈ range (m + 1 + 1), k n ≤
      A ^ ((1 + (d : ℝ) / 2) / p) * (4 * γ ^ 2) ^ (((d : ℝ) / 2 + (d : ℝ) * (d - 2) / 4) / p) := by
    have h1 := prod_shifted_geometric_le hγ hp hpp' hA1 hB1 (m + 1)
    rw [hT1, hT2] at h1
    exact (Finset.prod_le_prod₀ (fun n _ => hk0 n) hkA).trans h1
  set K : ℝ := A ^ ((1 + (d : ℝ) / 2) / p) *
    (4 * γ ^ 2) ^ (((d : ℝ) / 2 + (d : ℝ) * (d - 2) / 4) / p) with hK
  have hrad0 : rad (1 / 2) 0 = 1 := by rw [rad_zero]; norm_num
  have hrad1 : rad (1 / 2 : ℝ) 1 ≤ 1 := by
    have := rad_le (c := (1 / 2 : ℝ)) (by norm_num) 1; linarith
  -- the first step, with Holder
  have hfirst : a 1 ≤ ENNReal.ofReal (k 0) * a 0 := by
    have hpγ : ENNReal.ofReal p' ≤ ENNReal.ofReal (p * γ) := ENNReal.ofReal_le_ofReal hp'γ
    have hf1 : AEStronglyMeasurable f (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 1))) :=
      (hf.mono_measure (Measure.restrict_mono (euclideanBall_mono (by
        have := half_le_rad (c := (1 / 2 : ℝ)) (by norm_num) 1; linarith) hrad1) le_rfl)).aestronglyMeasurable
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpγ hf1
    rw [ENNReal.toReal_ofReal hp'0.le, ENNReal.toReal_ofReal (by positivity)] at hH
    have hmeas : (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 1))) Set.univ ≤
        ENNReal.ofReal V := by
      simp only [volumeOn, Measure.restrict_apply_univ]
      exact (measure_mono (euclideanBall_mono (by
        have := half_le_rad (c := (1 / 2 : ℝ)) (by norm_num) 1; linarith) hrad1)).trans hVol
    have ht0 : 0 ≤ 1 / p' - 1 / (p * γ) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hp'0 hp'γ
    have ht1 : 1 / p' - 1 / (p * γ) ≤ 1 / p := by
      have : 0 ≤ 1 / (p * γ) := by positivity
      have h2 : 1 / p' ≤ 1 / p := one_div_le_one_div_of_le hp hpp'
      linarith
    have hvol : (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 1))) Set.univ ^
        (1 / p' - 1 / (p * γ)) ≤ ENNReal.ofReal (V ^ (1 / p)) := by
      calc _ ≤ (ENNReal.ofReal V) ^ (1 / p' - 1 / (p * γ)) := ENNReal.rpow_le_rpow hmeas ht0
        _ = ENNReal.ofReal (V ^ (1 / p' - 1 / (p * γ))) :=
            ENNReal.ofReal_rpow_of_nonneg hV0.le ht0
        _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hV ht1)
    have h1 := hstep p hp (by
      have : p ≤ q := hpp'.trans hqp'
      linarith) (rad (1 / 2) 1) (rad (1 / 2) 0) (half_le_rad (by norm_num) _)
      (rad_succ_lt (by norm_num) 0) (by rw [hrad0])
    have hrewrite : ENNReal.ofReal (k 0) = ENNReal.ofReal (V ^ (1 / p)) *
        ENNReal.ofReal ((c₁ / (rad (1 / 2) 0 - rad (1 / 2) (0 + 1)) ^ 2 *
          (Λ * p ^ 2 / (1 - p) ^ 2 + 1)) ^ (1 / p)) := by
      simp only [hk, he0, ite_true]
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [hrewrite]
    simp only [ha, he0, he1]
    calc eLpNorm f (ENNReal.ofReal p') (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 1)))
        ≤ eLpNorm f (ENNReal.ofReal (p * γ))
            (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 1))) *
          (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 1))) Set.univ ^
            (1 / p' - 1 / (p * γ)) := hH
      _ ≤ (ENNReal.ofReal ((c₁ / (rad (1 / 2) 0 - rad (1 / 2) (0 + 1)) ^ 2 *
            (Λ * p ^ 2 / (1 - p) ^ 2 + 1)) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) 0)))) *
          ENNReal.ofReal (V ^ (1 / p)) := mul_le_mul' h1 hvol
      _ = _ := by ring
  have hc := chain_le a k hk0 (m + 1 + 1) (fun n hn => by
    by_cases h0 : n = 0
    · subst h0; exact hfirst
    · have hnm : n ≤ m + 1 := Nat.lt_succ_iff.1 hn
      have h1 : e n < 1 := lt_of_le_of_lt (he_le n hnm) hq
      have := hstep (e n) (hepos n) h1 (rad (1 / 2) (n + 1)) (rad (1 / 2) n)
        (half_le_rad (by norm_num) _) (rad_succ_lt (by norm_num) n)
        (by have := rad_le (c := 1 / 2) (by norm_num) n; linarith)
      have hkn : k n = (c₁ / (rad (1 / 2) n - rad (1 / 2) (n + 1)) ^ 2 *
          (Λ * e n ^ 2 / (1 - e n) ^ 2 + 1)) ^ (1 / e n) := by
        simp only [hk, h0, ite_false, one_mul]
      simp only [ha, he_succ n (by omega)]
      rw [hkn]
      exact this)
  have ha0 : a 0 = eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    simp only [ha, he0, hrad0]
  rw [ha0] at hc
  have hlast : e (m + 1 + 1) = q * γ := by
    rw [he_succ (m + 1) (by omega), ← hm]
    simp only [he, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
  have hmono := eLpNorm_ball_mono f (ENNReal.ofReal (q * γ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (half_le_rad (c := 1 / 2) (by norm_num) (m + 1 + 1))
  refine hmono.trans ?_
  have : a (m + 1 + 1) = eLpNorm f (ENNReal.ofReal (q * γ))
      (volumeOn (euclideanBall (0 : Vec d) (rad (1 / 2) (m + 1 + 1)))) := by
    simp only [ha, hlast]
  rw [← this]
  exact hc.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hprod) le_rfl)

end PDE.DGNMMoser
