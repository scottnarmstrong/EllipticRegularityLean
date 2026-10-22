module

public import EllipticRegularity.DeGiorgi.MoserIter.SmallIterateB

/-!
# The two estimates of (4.68) for a function with the one-step estimate

Combines the geometric and shifted cases of the small-exponent iteration into the two
`p`-th power estimates of Step 3, with the explicit constant
`(16 c₁ V)^{(d+2)/2} (4γ²)^{d/2 + d(d-2)/4}`.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped ENNReal

namespace PDE.DGNMMoser

/-- The constant of the weak Harnack estimate (4.68). -/
noncomputable def smallConst (d : ℕ) (c₁ V : ℝ) : ℝ :=
  (16 * c₁ * V) ^ (((d : ℝ) + 2) / 2) *
    (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) / 2 + (d : ℝ) * (d - 2) / 4)

theorem smallConst_pos {d : ℕ} (hd : 3 ≤ d) {c₁ V : ℝ} (hc₁ : 1 ≤ c₁) (hV : 1 ≤ V) :
    0 < smallConst d c₁ V := by
  unfold smallConst
  have h1 : 0 < 16 * c₁ * V := by nlinarith
  have hγ := one_lt_gamma hd
  have h2 : 0 < 4 * ((d : ℝ) / (d - 2)) ^ 2 := by positivity
  positivity

theorem exp_case_A {d : ℕ} (hd : 3 ≤ d) {c₁ V X : ℝ} (hc₁ : 1 ≤ c₁) (hV : 1 ≤ V) (hX : 0 ≤ X) :
    (16 * c₁ * V * X) ^ ((d : ℝ) / 2) * (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4)
      ≤ smallConst d c₁ V * X ^ ((d : ℝ) / 2) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 1 ≤ 16 * c₁ * V := by nlinarith
  have hγ := one_lt_gamma hd
  have hB : 1 ≤ 4 * ((d : ℝ) / (d - 2)) ^ 2 := by nlinarith
  unfold smallConst
  have h0 : 0 ≤ 16 * c₁ * V := by linarith
  rw [Real.mul_rpow h0 hX]
  have e1 : (16 * c₁ * V) ^ ((d : ℝ) / 2) ≤ (16 * c₁ * V) ^ (((d : ℝ) + 2) / 2) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have e2 : (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) * (d - 2) / 4) ≤
      (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) / 2 + (d : ℝ) * (d - 2) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hXp : 0 ≤ X ^ ((d : ℝ) / 2) := Real.rpow_nonneg hX _
  have := mul_le_mul e1 e2 (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg h0 _)
  nlinarith [mul_le_mul_of_nonneg_right this hXp]

theorem exp_case_B {d : ℕ} {c₁ V X : ℝ} (hc₁ : 1 ≤ c₁) (hV : 1 ≤ V) (hX : 0 ≤ X) :
    (16 * c₁ * V * X) ^ (1 + (d : ℝ) / 2) *
        (4 * ((d : ℝ) / (d - 2)) ^ 2) ^ ((d : ℝ) / 2 + (d : ℝ) * (d - 2) / 4)
      = smallConst d c₁ V * X ^ (((d : ℝ) + 2) / 2) := by
  have h1 : 1 ≤ 16 * c₁ * V := by nlinarith
  unfold smallConst
  rw [Real.mul_rpow (by positivity) hX, show 1 + (d : ℝ) / 2 = ((d : ℝ) + 2) / 2 by ring]
  ring

/-- The two `p`-th power estimates of Step 3. -/
theorem small_bounds {d : ℕ} (hd : 3 ≤ d) {f : Vec d → ℝ}
    (hf : AEMeasurable f (volumeOn (euclideanBall (0 : Vec d) 1)))
    {c₁ Λ V : ℝ} (hc₁ : 1 ≤ c₁) (hΛ : 0 ≤ Λ) (hV : 1 ≤ V)
    (hVol : volume (euclideanBall (0 : Vec d) 1) ≤ ENNReal.ofReal V)
    (hstep : SmallStep f c₁ Λ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) :
    (eLpNorm f (ENNReal.ofReal (q * ((d : ℝ) / (d - 2))))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
      ENNReal.ofReal (smallConst d c₁ V * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) *
        (eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p ∧
    ∀ m : ℕ, p * ((d : ℝ) / (d - 2)) ^ m = q →
      (eLpNorm f (ENNReal.ofReal (q * ((d : ℝ) / (d - 2))))
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
      ENNReal.ofReal (smallConst d c₁ V * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) *
        (eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p := by
  set γ : ℝ := (d : ℝ) / (d - 2) with hγdef
  have hγ : 1 < γ := one_lt_gamma hd
  have hc0 : 0 < c₁ := by linarith
  have hCpos := smallConst_pos hd hc₁ hV
  set X : ℝ := Λ * p ^ 2 / (1 - q) ^ 2 + 1 with hX
  have hX1 : 1 ≤ X := by rw [hX]; have : 0 ≤ Λ * p ^ 2 / (1 - q) ^ 2 := by positivity
                         linarith
  have hX0 : 0 ≤ X := by linarith
  -- power form of a bound `S ≤ ofReal K * E`
  have powform : ∀ (S E : ℝ≥0∞) (K R : ℝ), 0 ≤ K → S ≤ ENNReal.ofReal K * E → K ^ p ≤ R →
      S ^ p ≤ ENNReal.ofReal R * E ^ p := fun S E K R hK h hR => by
    calc S ^ p ≤ (ENNReal.ofReal K * E) ^ p := ENNReal.rpow_le_rpow h hp.le
      _ = ENNReal.ofReal (K ^ p) * E ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg hK hp.le]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hR) le_rfl
  have hA0 : 0 ≤ 16 * c₁ * V * X := by positivity
  have hB0 : 0 ≤ 4 * γ ^ 2 := by positivity
  have caseA : ∀ m : ℕ, p * γ ^ m = q →
      (eLpNorm f (ENNReal.ofReal (q * γ)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
      ENNReal.ofReal (smallConst d c₁ V * X ^ ((d : ℝ) / 2)) *
        (eLpNorm f (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p := by
    intro m hm
    refine powform _ _ _ _ (by positivity)
      (small_iteration_geometric hd hc₁ hΛ hV hstep hp hq m hm) ?_
    rw [rpow_div_mul_rpow_pow hA0 hB0 hp]
    exact exp_case_A hd hc₁ hV hX0
  refine ⟨?_, caseA⟩
  -- the first estimate: pick `n` with `γ^n ≤ q/p < γ^(n+1)`
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := q / p) (y := γ)
    (by rw [le_div_iff₀ hp]; linarith) hγ
  have hγn : 0 < γ ^ n := by positivity
  have hpn : p * γ ^ n ≤ q := by rwa [le_div_iff₀ hp, mul_comm] at hn1
  have hqn : q < p * γ ^ (n + 1) := by rw [div_lt_iff₀ hp, mul_comm] at hn2; exact hn2
  by_cases heq : p * γ ^ n = q
  · refine (caseA n heq).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine mul_le_mul_of_nonneg_left ?_ hCpos.le
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  · set p' : ℝ := q / γ ^ n with hp'
    have hp'm : p' * γ ^ n = q := by rw [hp']; field_simp
    have hpp' : p ≤ p' := by rw [hp', le_div_iff₀ hγn]; exact hpn
    have hp'γ : p' ≤ p * γ := by
      rw [hp', div_le_iff₀ hγn]; rw [pow_succ] at hqn; nlinarith
    refine powform _ _ _ _ (by positivity)
      (small_iteration_shifted hd hf hc₁ hΛ hV hVol hstep hp hpp' hp'γ hq n hp'm) ?_
    rw [rpow_div_mul_rpow_pow hA0 hB0 hp]
    exact le_of_eq (exp_case_B hc₁ hV hX0)

end PDE.DGNMMoser
