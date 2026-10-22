module

public import EllipticRegularity.DeGiorgi.MoserIter.Scalar
public import EllipticRegularity.DeGiorgi.MoserIter.Chain

/-!
# Scalar estimates for the small-exponent Moser iteration

Bounds on the one-step constants `Λ e²/(1-e)² + 1` along the exponents of the iteration
of (4.72), and the `p`-th power of the final constant.
-/

@[expose] public section

namespace PDE.DGNMMoser

/-- `(A^(e₁/p) * B^(e₂/p))^p = A^e₁ * B^e₂`. -/
theorem rpow_div_mul_rpow_pow {A B e₁ e₂ p : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 < p) :
    (A ^ (e₁ / p) * B ^ (e₂ / p)) ^ p = A ^ e₁ * B ^ e₂ := by
  rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _), ← Real.rpow_mul hA,
    ← Real.rpow_mul hB, div_mul_cancel₀ _ hp.ne', div_mul_cancel₀ _ hp.ne']

/-- The one-step constant along the iteration is at most `(γ²)^n X`. -/
theorem oneStepConst_le {Λ e p q γ : ℝ} {n : ℕ} (hΛ : 0 ≤ Λ) (he0 : 0 < e) (heq : e ≤ q)
    (hq1 : q < 1) (he2 : e ^ 2 ≤ (γ ^ 2) ^ n * p ^ 2) (hγn : 1 ≤ (γ ^ 2) ^ n) :
    Λ * e ^ 2 / (1 - e) ^ 2 + 1 ≤ (γ ^ 2) ^ n * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) := by
  have h1q : 0 < 1 - q := by linarith
  have hden : (1 - q) ^ 2 ≤ (1 - e) ^ 2 := by nlinarith
  have h1 : Λ * e ^ 2 / (1 - e) ^ 2 ≤ Λ * ((γ ^ 2) ^ n * p ^ 2) / (1 - q) ^ 2 := by
    calc Λ * e ^ 2 / (1 - e) ^ 2 ≤ Λ * e ^ 2 / (1 - q) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ _ := by gcongr
  have h2 : Λ * ((γ ^ 2) ^ n * p ^ 2) / (1 - q) ^ 2 =
      (γ ^ 2) ^ n * (Λ * p ^ 2 / (1 - q) ^ 2) := by ring
  nlinarith

/-- The `k n ≤ (A B^n)^(1/e)` bound for one step of the iteration. -/
theorem stepFactor_le {c₁ Xn X V γ e : ℝ} {n : ℕ} (hc₁ : 0 ≤ c₁) (hV : 1 ≤ V) (hX0 : 0 ≤ X)
    (hXn0 : 0 ≤ Xn) (hXn : Xn ≤ (γ ^ 2) ^ n * X) (he : 0 < e) :
    (c₁ * (16 * 4 ^ n) * Xn) ^ (1 / e) ≤ ((16 * c₁ * V * X) * (4 * γ ^ 2) ^ n) ^ e⁻¹ := by
  rw [one_div]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  calc c₁ * (16 * 4 ^ n) * Xn ≤ c₁ * (16 * 4 ^ n) * ((γ ^ 2) ^ n * X) := by gcongr
    _ = (16 * c₁ * X) * (4 * γ ^ 2) ^ n := by rw [mul_pow]; ring
    _ ≤ (16 * c₁ * V * X) * (4 * γ ^ 2) ^ n := by
        have h : 16 * c₁ * X ≤ 16 * c₁ * V * X := by nlinarith [mul_nonneg hc₁ hX0]
        exact mul_le_mul_of_nonneg_right h (by positivity)

end PDE.DGNMMoser
