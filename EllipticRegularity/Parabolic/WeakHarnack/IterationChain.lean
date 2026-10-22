module

public import EllipticRegularity.DeGiorgi.MoserIter.Chain
public import EllipticRegularity.DeGiorgi.MoserIter.Scalar

/-!
# Geometric chains of reverse Hölder steps on nested sets

Abstract measure-theoretic iteration: from a one-step estimate
`‖f‖_{χp, U σ'} ≤ (C(p) (σ-σ')^{-m})^{1/p} ‖f‖_{p, U σ}` we iterate along the exponents
`p₀ χ^k` on the sets `U (σ' + (σ-σ') 2^{-k})`, and collect the product of the constants.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PDE.ParabIter

variable {X : Type*} [MeasurableSpace X]

/-- `(g 2^{-(n+1)})^{-m} = g^{-m} 2^m (2^m)^n`. -/
theorem gap_rpow (g m : ℝ) (hg : 0 < g) (n : ℕ) :
    (g * ((2 : ℝ) ^ (n + 1))⁻¹) ^ (-m) = g ^ (-m) * 2 ^ m * (2 ^ m) ^ n := by
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [Real.mul_rpow hg.le (inv_nonneg.mpr h2.le), Real.inv_rpow h2.le, Real.rpow_neg h2.le,
    inv_inv, mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast (2 ^ m), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  push_cast
  ring

/-- Iterating a one-step estimate along the exponents `p₀ χ^k`. -/
theorem chain_geometric (ν : Measure X) (U : ℝ → Set X) (f : X → ℝ) (δ χ m : ℝ)
    (hδ : 0 < δ) (hχ : 1 < χ)
    (P : ℝ → Prop) (Cf : ℝ → ℝ)
    (hstep : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p → P p →
      eLpNorm f (ENNReal.ofReal (χ * p)) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((Cf p * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) (ν.restrict (U σ)))
    (hUmono : ∀ σ' σ, δ ≤ σ' → σ' ≤ σ → σ ≤ 1 → U σ' ⊆ U σ)
    {p₀ A₁ B₁ : ℝ} (hm : 0 < m) (hp₀ : 0 < p₀) (hA₁ : 1 ≤ A₁) (hB₁ : 1 ≤ B₁) (N : ℕ)
    (hP : ∀ k < N, P (p₀ * χ ^ k))
    (hC0 : ∀ k < N, 0 ≤ Cf (p₀ * χ ^ k))
    (hC : ∀ k < N, Cf (p₀ * χ ^ k) ≤ A₁ * B₁ ^ k)
    {σ' σ : ℝ} (h1 : δ ≤ σ') (h2 : σ' < σ) (h3 : σ ≤ 1) :
    eLpNorm f (ENNReal.ofReal (p₀ * χ ^ N)) (ν.restrict (U σ')) ≤
      ENNReal.ofReal ((A₁ * 2 ^ m * (σ - σ') ^ (-m)) ^ (χ / (χ - 1) / p₀) *
        (B₁ * 2 ^ m) ^ (χ / (χ - 1) ^ 2 / p₀)) *
      eLpNorm f (ENNReal.ofReal p₀) (ν.restrict (U σ)) := by
  set g : ℝ := σ - σ' with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hg1 : g ≤ 1 := by rw [hg]; linarith
  set s : ℕ → ℝ := fun n => σ' + g * ((2 : ℝ) ^ n)⁻¹ with hs
  have hs_ge : ∀ n, σ' ≤ s n := fun n => by
    simp only [hs]; have : 0 < g * ((2 : ℝ) ^ n)⁻¹ := by positivity
    linarith
  have hs_le : ∀ n, s n ≤ σ := fun n => by
    simp only [hs]
    have : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have : g * ((2 : ℝ) ^ n)⁻¹ ≤ g * 1 := by gcongr
    linarith
  have hs_sub : ∀ n, s n - s (n + 1) = g * ((2 : ℝ) ^ (n + 1))⁻¹ := fun n => by
    simp only [hs]; rw [pow_succ]; field_simp; ring
  have hs_lt : ∀ n, s (n + 1) < s n := fun n => by
    have := hs_sub n
    have : 0 < g * ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
    linarith
  set e : ℕ → ℝ := fun n => p₀ * χ ^ n with he
  have he0 : ∀ n, 0 < e n := fun n => by
    have : 0 < χ := by linarith
    simp only [he]; positivity
  have he_succ : ∀ n, e (n + 1) = χ * e n := fun n => by simp only [he, pow_succ]; ring
  set a : ℕ → ℝ≥0∞ := fun n => eLpNorm f (ENNReal.ofReal (e n)) (ν.restrict (U (s n))) with ha
  set k : ℕ → ℝ := fun n =>
    (max (Cf (e n)) 0 * (g * ((2 : ℝ) ^ (n + 1))⁻¹) ^ (-m)) ^ (1 / e n) with hk
  have hk0 : ∀ n, 0 ≤ k n := fun n =>
    Real.rpow_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)) _
  have hchain := PDE.DGNMMoser.chain_le a k hk0 N (fun n hn => by
    have hst := hstep (s (n + 1)) (s n) (le_trans h1 (hs_ge _)) (hs_lt n)
      (le_trans (hs_le n) h3) (e n) (he0 n) (hP n hn)
    have hk' : k n = (Cf (e n) * (s n - s (n + 1)) ^ (-m)) ^ (1 / e n) := by
      simp only [hk]; rw [hs_sub, max_eq_left (hC0 n hn)]
    show eLpNorm f (ENNReal.ofReal (e (n + 1))) (ν.restrict (U (s (n + 1)))) ≤
      ENNReal.ofReal (k n) * a n
    rw [he_succ, hk']
    exact hst)
  have hA : 1 ≤ A₁ * 2 ^ m * g ^ (-m) := by
    have h2m : (1 : ℝ) ≤ 2 ^ m := Real.one_le_rpow (by norm_num) hm.le
    have hgm : (1 : ℝ) ≤ g ^ (-m) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hg0 hg1 (by linarith)
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hB : 1 ≤ B₁ * 2 ^ m := by
    have h2m : (1 : ℝ) ≤ 2 ^ m := Real.one_le_rpow (by norm_num) hm.le
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hγ0 : 0 < χ := by linarith
  have hprod : ∏ n ∈ range N, k n ≤
      (A₁ * 2 ^ m * g ^ (-m)) ^ (χ / (χ - 1) / p₀) *
        (B₁ * 2 ^ m) ^ (χ / (χ - 1) ^ 2 / p₀) := by
    refine le_trans (Finset.prod_le_prod₀ (fun n _ => hk0 n) (fun n hn => ?_))
      (PDE.DGNMMoser.prod_geometric_le hχ hp₀ hA hB N)
    have hn' := Finset.mem_range.mp hn
    show (max (Cf (e n)) 0 * (g * ((2 : ℝ) ^ (n + 1))⁻¹) ^ (-m)) ^ (1 / e n) ≤
      ((A₁ * 2 ^ m * g ^ (-m)) * (B₁ * 2 ^ m) ^ n) ^ (p₀ * χ ^ n)⁻¹
    rw [one_div]
    have hG : 0 ≤ g ^ (-m) * 2 ^ m * (2 ^ m) ^ n := by positivity
    refine Real.rpow_le_rpow (mul_nonneg (le_max_right _ _)
      (Real.rpow_nonneg (by positivity) _)) ?_ (inv_nonneg.mpr (he0 n).le)
    rw [gap_rpow g m hg0 n, max_eq_left (hC0 n hn')]
    calc Cf (e n) * (g ^ (-m) * 2 ^ m * (2 ^ m) ^ n)
        ≤ (A₁ * B₁ ^ n) * (g ^ (-m) * 2 ^ m * (2 ^ m) ^ n) :=
          mul_le_mul_of_nonneg_right (hC n hn') hG
      _ = _ := by rw [mul_pow]; ring
  have hs0 : s 0 = σ := by simp [hs, hg]
  have hsN : U σ' ⊆ U (s N) :=
    hUmono σ' (s N) h1 (hs_ge N) ((hs_le N).trans h3)
  calc eLpNorm f (ENNReal.ofReal (p₀ * χ ^ N)) (ν.restrict (U σ'))
      ≤ a N := eLpNorm_mono_measure f (Measure.restrict_mono hsN le_rfl)
    _ ≤ ENNReal.ofReal (∏ n ∈ range N, k n) * a 0 := hchain
    _ ≤ _ := by
      have ha0 : a 0 = eLpNorm f (ENNReal.ofReal p₀) (ν.restrict (U σ)) := by
        simp only [ha, he, pow_zero, mul_one, hs0]
      rw [ha0]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hprod) le_rfl

end PDE.ParabIter
