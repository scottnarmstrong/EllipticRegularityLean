module

public import EllipticRegularity.Ch4.Spagnolo.FluxVanish
public import EllipticRegularity.Ch4.Spagnolo.Approximation

/-!
# The integrated differential inequality

Manuscript Theorem 4.24, Step 3, integrated against radial profiles. For a smooth
nonincreasing profile `H` vanishing on `[s₀, ∞)`, `s₀ < 1`, with `k = -H' ≥ 0`,
`σ = a ∇u` and `e = ∇u · a ∇u`,
`∫_{B₁} H(|x|²) e ≤ √Λ ∫_{B₁} k(|x|²) |x|² e`.

This is the manuscript's `φ(r) ≤ ½ Λ^{1/2} r φ'(r)` tested against `k`. The proof:
the energy identity gives `∫ H e = 2 ∫ k u σ·x`; the vanishing circle flux
allows us to subtract any continuous radial function `c(|x|)` from `u`; the
pointwise Young inequality with the planar matrix inequality bounds
`2 k (u - c) σ·x` by `√Λ k ((u - c)² + |x|² e - (x⊥·∇u)²)`; and the Wirtinger
inequality on circles, applied to smooth approximants `v_n` of `u` with
`c = c_{v_n}` (the circle means of `v_n`), absorbs `(u - c)²` into
`(x⊥·∇u)²` in the limit.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set Filter
open scoped Topology

private theorem sq_add_le_eps (p q ε : ℝ) (hε : 0 < ε) :
    (p + q) ^ 2 ≤ (1 + ε) * p ^ 2 + (1 + ε⁻¹) * q ^ 2 := by
  have h : (1 + ε) * p ^ 2 + (1 + ε⁻¹) * q ^ 2 - (p + q) ^ 2 = ε⁻¹ * (ε * p - q) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ ε⁻¹ * (ε * p - q) ^ 2 := mul_nonneg (inv_nonneg.2 hε.le) (sq_nonneg _)
  linarith

/-- Weighted form of `(f + g)² ≤ (1 + ε) f² + (1 + ε⁻¹) g²`. -/
theorem weighted_sq_add_le {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ t, 0 ≤ k t)
    {f g : Vec 2 → ℝ} (hf : MemL2On (euclideanBall (0 : Vec 2) 1) f)
    (hg : MemL2On (euclideanBall (0 : Vec 2) 1) g) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in euclideanBall (0 : Vec 2) 1, k (vecNormSq x) * (f x + g x) ^ 2 ≤
      (1 + ε) * (∫ x in euclideanBall (0 : Vec 2) 1, k (vecNormSq x) * f x ^ 2) +
        (1 + ε⁻¹) * ∫ x in euclideanBall (0 : Vec 2) 1, k (vecNormSq x) * g x ^ 2 := by
  have hkc : Continuous (fun x : Vec 2 => k (vecNormSq x)) := hk.comp continuous_vecNormSq
  have hI1 := integrableOn_continuous_mul hkc hf.integrable_sq
  have hI2 := integrableOn_continuous_mul hkc hg.integrable_sq
  have hI3 := integrableOn_continuous_mul hkc (hf.add hg).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hI1.const_mul _)
    (hI2.const_mul _)]
  refine setIntegral_mono_on hI3 ((hI1.const_mul _).add (hI2.const_mul _))
    (measurableSet_euclideanBall _ _) fun x _ => ?_
  have := mul_le_mul_of_nonneg_left (sq_add_le_eps (f x) (g x) ε hε) (hk0 (vecNormSq x))
  linarith

section Solution

variable {Λ : ℝ} {a : CoeffField 2}

local notation "𝔹" => euclideanBall (0 : Vec 2) 1

/-- **Integrated differential inequality.** For a smooth nonincreasing profile
`H` vanishing on `[s₀, ∞)`, `s₀ < 1`:
`∫_{B₁} H(|x|²) ∇u·a∇u ≤ √Λ ∫_{B₁} (-H'(|x|²)) |x|² ∇u·a∇u`. -/
theorem integral_radial_energy_le (hW : WirtingerStatement)
    (hmeas : ∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 2) 1)))
    (hsymm : ∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i)
    (hell : ∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x))
    (u : H1Function (euclideanBall (0 : Vec 2) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) 0)
    {H : ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hH' : ∀ t, deriv H t ≤ 0) {s0 : ℝ}
    (hs0 : s0 < 1) (hHs : ∀ t, s0 ≤ t → H t = 0) :
    ∫ x in euclideanBall (0 : Vec 2) 1,
        H (vecNormSq x) * vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      Real.sqrt Λ * ∫ x in euclideanBall (0 : Vec 2) 1,
        -deriv H (vecNormSq x) *
          (vecNormSq x * vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
  -- notation
  have hBm : MeasurableSet 𝔹 := measurableSet_euclideanBall _ _
  set k : ℝ → ℝ := fun t => -deriv H t with hkdef
  have hk : Continuous k := (hH.continuous_deriv (by simp)).neg
  have hk0 : ∀ t, 0 ≤ k t := fun t => by simp only [hkdef]; linarith [hH' t]
  have hkc : Continuous (fun x : Vec 2 => k (vecNormSq x)) := hk.comp continuous_vecNormSq
  set e : Vec 2 → ℝ := fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)) with he
  set σx : Vec 2 → ℝ := fun x => vecDot (matVecMul (a x) (u.grad x)) x with hσx
  set P : Vec 2 → ℝ := fun x => perpDot x (u.grad x) with hP
  have he_int : IntegrableOn e 𝔹 := integrableOn_energy hmeas hell u
  have hσx_int : IntegrableOn σx 𝔹 := integrableOn_flux_dot hmeas hell u
  have huσ_int : IntegrableOn (fun x => u x * σx x) 𝔹 := integrableOn_mul_flux_dot hmeas hell u
  have hPL2 : MemL2On 𝔹 P := memL2On_perpDot_grad u
  -- the right-hand side
  set A : ℝ := ∫ x in 𝔹, k (vecNormSq x) * (vecNormSq x * e x) with hA
  set Pu : ℝ := ∫ x in 𝔹, k (vecNormSq x) * P x ^ 2 with hPu
  have hPu0 : 0 ≤ Pu := setIntegral_nonneg hBm fun x _ => mul_nonneg (hk0 _) (sq_nonneg _)
  have hRHS : Real.sqrt Λ * ∫ x in 𝔹, -deriv H (vecNormSq x) * (vecNormSq x * e x) =
      Real.sqrt Λ * A := rfl
  rw [hRHS]
  -- the energy identity: `∫ H e = 2 ∫ k u σx`
  have hF2 := integral_radial_mul_energy_add_eq_zero hmeas hell u hsol hH hs0 hHs
  have hLHS : ∫ x in 𝔹, H (vecNormSq x) * e x =
      ∫ x in 𝔹, 2 * (k (vecNormSq x) * (u x * σx x)) := by
    rw [integral_const_mul]
    have : ∫ x in 𝔹, k (vecNormSq x) * (u x * σx x) =
        -∫ x in 𝔹, deriv H (vecNormSq x) * (u x * σx x) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hkdef]; ring
    rw [this]
    linarith
  -- smooth approximants and their circle means
  obtain ⟨v, hv, hvconv, hgconv⟩ := exists_smooth_approximation u
  set c : ℕ → ℝ → ℝ := fun n => circleMean (v n) with hc
  have hcc : ∀ n, Continuous (c n) := fun n => continuous_circleMean (hv n).continuous
  have hcx : ∀ n, Continuous (fun x : Vec 2 => c n (vecEuclideanNorm x)) :=
    fun n => (hcc n).comp continuous_vecEuclideanNorm
  have huc : ∀ n, MemL2On 𝔹 (fun x => u x - c n (vecEuclideanNorm x)) :=
    fun n => u.memL2.sub (memL2On_of_continuous (hcx n))
  -- Step (a): `∫ H e ≤ √Λ (Iu n + A - Pu)`
  have hstep_a : ∀ n, ∫ x in 𝔹, H (vecNormSq x) * e x ≤
      Real.sqrt Λ * ((∫ x in 𝔹, k (vecNormSq x) * (u x - c n (vecEuclideanNorm x)) ^ 2) +
        A - Pu) := by
    intro n
    -- subtract the circle mean using the vanishing flux
    have horth : ∫ x in 𝔹, k (vecNormSq x) * c n (vecEuclideanNorm x) * σx x = 0 := by
      have h := integral_radial_mul_flux_dot_eq_zero hmeas hell u hsol
        (R := fun ρ => k (ρ ^ 2) * c n ρ) ((hk.comp (continuous_pow 2)).mul (hcc n))
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [σx, vecEuclideanNorm, Real.sq_sqrt (vecNormSq_nonneg x)]
    have hI1 : IntegrableOn (fun x => 2 * (k (vecNormSq x) * (u x * σx x))) 𝔹 :=
      (integrableOn_continuous_mul hkc huσ_int).const_mul 2
    have hI2 : IntegrableOn (fun x => 2 * (k (vecNormSq x) * c n (vecEuclideanNorm x) * σx x))
        𝔹 := (integrableOn_continuous_mul (hkc.mul (hcx n)) hσx_int).const_mul 2
    have hsplit : ∫ x in 𝔹, 2 * (k (vecNormSq x) * (u x * σx x)) =
        ∫ x in 𝔹, 2 * (k (vecNormSq x) * ((u x - c n (vecEuclideanNorm x)) * σx x)) := by
      have h0 : ∫ x in 𝔹, 2 * (k (vecNormSq x) * c n (vecEuclideanNorm x) * σx x) = 0 := by
        rw [integral_const_mul, horth, mul_zero]
      rw [← sub_zero (∫ x in 𝔹, 2 * (k (vecNormSq x) * (u x * σx x))), ← h0,
        ← integral_sub hI1 hI2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [hLHS, hsplit]
    -- pointwise Young
    have hJ1 : IntegrableOn (fun x => k (vecNormSq x) *
        (u x - c n (vecEuclideanNorm x)) ^ 2) 𝔹 :=
      integrableOn_continuous_mul hkc (huc n).integrable_sq
    have hJ2 : IntegrableOn (fun x => k (vecNormSq x) * (vecNormSq x * e x)) 𝔹 :=
      integrableOn_continuous_mul hkc (integrableOn_continuous_mul continuous_vecNormSq he_int)
    have hJ3 : IntegrableOn (fun x => k (vecNormSq x) * P x ^ 2) 𝔹 :=
      integrableOn_continuous_mul hkc hPL2.integrable_sq
    have hlhs_int : IntegrableOn
        (fun x => 2 * (k (vecNormSq x) * ((u x - c n (vecEuclideanNorm x)) * σx x))) 𝔹 := by
      refine (hI1.sub hI2).congr_fun (fun x _ => ?_) hBm
      simp only [Pi.sub_apply]; ring
    have hrhs_int : IntegrableOn (fun x => Real.sqrt Λ * (k (vecNormSq x) *
        (u x - c n (vecEuclideanNorm x)) ^ 2 + k (vecNormSq x) * (vecNormSq x * e x) -
          k (vecNormSq x) * P x ^ 2)) 𝔹 := ((hJ1.add hJ2).sub hJ3).const_mul _
    have hrhs : ∫ x in 𝔹, Real.sqrt Λ * (k (vecNormSq x) *
        (u x - c n (vecEuclideanNorm x)) ^ 2 + k (vecNormSq x) * (vecNormSq x * e x) -
          k (vecNormSq x) * P x ^ 2) =
        Real.sqrt Λ * ((∫ x in 𝔹, k (vecNormSq x) * (u x - c n (vecEuclideanNorm x)) ^ 2) +
          A - Pu) := by
      have hJ12 : IntegrableOn (fun x => k (vecNormSq x) *
          (u x - c n (vecEuclideanNorm x)) ^ 2 + k (vecNormSq x) * (vecNormSq x * e x)) 𝔹 :=
        hJ1.add hJ2
      rw [integral_const_mul, integral_sub hJ12 hJ3, integral_add hJ1 hJ2]
    rw [← hrhs]
    refine setIntegral_mono_on hlhs_int hrhs_int hBm fun x hx => ?_
    have hY := mul_vecDot_le_young (hell x hx) (hsymm x hx 0 1) x (u.grad x)
      (u x - c n (vecEuclideanNorm x))
    have hkx := hk0 (vecNormSq x)
    have h2 := mul_le_mul_of_nonneg_left hY (mul_nonneg zero_le_two hkx)
    simp only [σx, e, P]
    nlinarith [h2]
  -- Step (b)-(d): absorb `(u - c_n)²` via Wirtinger for `v_n`
  have hvc : ∀ n, Continuous (v n) := fun n => (hv n).continuous
  have hgradc : ∀ n i, Continuous (fun x => classicalGradient (v n) x i) := fun n i =>
    ((hv n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hPv : ∀ n, Continuous (fun x => perpDot x (classicalGradient (v n) x)) := by
    intro n
    unfold perpDot
    exact ((continuous_apply 0).mul (hgradc n 1)).sub ((continuous_apply 1).mul (hgradc n 0))
  set Duv : ℕ → ℝ := fun n => ∫ x in 𝔹, k (vecNormSq x) * (u x - v n x) ^ 2 with hDuv
  set Dp : ℕ → ℝ := fun n => ∫ x in 𝔹, k (vecNormSq x) *
    (perpDot x (classicalGradient (v n) x) - P x) ^ 2 with hDp
  have hbound : ∀ n, ∀ ε : ℝ, 0 < ε → ∫ x in 𝔹, H (vecNormSq x) * e x ≤
      Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu + (1 + ε) * (1 + ε⁻¹) * Dp n +
        (1 + ε⁻¹) * Duv n) := by
    intro n ε hε
    -- (b)
    have hb : (∫ x in 𝔹, k (vecNormSq x) * (u x - c n (vecEuclideanNorm x)) ^ 2) ≤
        (1 + ε) * (∫ x in 𝔹, k (vecNormSq x) * (v n x - c n (vecEuclideanNorm x)) ^ 2) +
          (1 + ε⁻¹) * Duv n := by
      have h := weighted_sq_add_le hk hk0
        (memL2On_of_continuous ((hvc n).sub (hcx n))) (u.memL2.sub
          (memL2On_of_continuous (hvc n))) hε
      convert h using 2
      funext x
      simp only [Pi.sub_apply]; ring
    -- (c)
    have hc' : (∫ x in 𝔹, k (vecNormSq x) * (v n x - c n (vecEuclideanNorm x)) ^ 2) ≤
        ∫ x in 𝔹, k (vecNormSq x) * perpDot x (classicalGradient (v n) x) ^ 2 :=
      weighted_circle_wirtinger hW (hv n) hk hk0
    -- (d)
    have hd : (∫ x in 𝔹, k (vecNormSq x) * perpDot x (classicalGradient (v n) x) ^ 2) ≤
        (1 + ε) * Pu + (1 + ε⁻¹) * Dp n := by
      have h := weighted_sq_add_le hk hk0 hPL2
        ((memL2On_of_continuous (hPv n)).sub hPL2) hε
      convert h using 2
      funext x
      simp only [Pi.sub_apply]; ring
    have ha := hstep_a n
    have hsq : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
    have hε1 : 0 ≤ 1 + ε := by linarith
    calc ∫ x in 𝔹, H (vecNormSq x) * e x
        ≤ Real.sqrt Λ * ((∫ x in 𝔹, k (vecNormSq x) *
            (u x - c n (vecEuclideanNorm x)) ^ 2) + A - Pu) := ha
      _ ≤ Real.sqrt Λ * ((1 + ε) * ((1 + ε) * Pu + (1 + ε⁻¹) * Dp n) +
            (1 + ε⁻¹) * Duv n + A - Pu) := by
          refine mul_le_mul_of_nonneg_left ?_ hsq
          have := mul_le_mul_of_nonneg_left (hc'.trans hd) hε1
          linarith
      _ = Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu + (1 + ε) * (1 + ε⁻¹) * Dp n +
            (1 + ε⁻¹) * Duv n) := by ring
  -- limits
  have hDuv0 : Tendsto Duv atTop (𝓝 0) :=
    tendsto_weighted_sq_sub u.memL2 hvc hvconv hk hk0
  have hDp0 : Tendsto Dp atTop (𝓝 0) :=
    tendsto_weighted_sq_perpDot_sub u.gradMemL2 hv hgconv hk hk0
  have hεbound : ∀ ε : ℝ, 0 < ε → ∫ x in 𝔹, H (vecNormSq x) * e x ≤
      Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu) := by
    intro ε hε
    have hlim : Tendsto (fun n => Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu +
        (1 + ε) * (1 + ε⁻¹) * Dp n + (1 + ε⁻¹) * Duv n)) atTop
        (𝓝 (Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu + (1 + ε) * (1 + ε⁻¹) * 0 +
          (1 + ε⁻¹) * 0))) :=
      ((tendsto_const_nhds.add (hDp0.const_mul _)).add (hDuv0.const_mul _)).const_mul _
    simp only [mul_zero, add_zero] at hlim
    exact ge_of_tendsto hlim (Eventually.of_forall fun n => hbound n ε hε)
  have hlim : Tendsto (fun ε : ℝ => Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu))
      (𝓝[>] 0) (𝓝 (Real.sqrt Λ * A)) := by
    have hcont : Continuous (fun ε : ℝ => Real.sqrt Λ * (A + ((1 + ε) ^ 2 - 1) * Pu)) := by
      fun_prop
    have h := hcont.tendsto 0
    simp only [add_zero, one_pow, sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hεbound ε hε)

end Solution

end PDE.Ch4Spagnolo
