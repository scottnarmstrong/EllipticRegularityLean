module

public import PDEFoundation.PDE.DGNM.ProductTest

/-!
# The absorption step of Caccioppoli-type arguments

Abstract form of the step used in Lemma 4.1, the Moser test computations
(4.62, (4.70)) and the logarithmic energy estimate: if a gradient
field `ξ ∈ L²` satisfies, for some `c₁ > 0` and `c₂ ∈ ℝ`,

`c₁ ∫ η² ξ·aξ + c₂ ∫ η ω (aξ·∇η) ≤ 0`,

then `∫ η² ξ·aξ ≤ (c₂² Λ / c₁²) ∫ ω² |∇η|²`, and consequently
`∫ |η ξ + ω ∇η|² ≤ (2 c₂² Λ / c₁² + 2) ∫ ω² |∇η|²`.
-/

@[expose] public section

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- Parameterized pointwise Young bound for the cross term, with the
energy-adapted flux bound `|Aξ|² ≤ Λ ξ·Aξ`. -/
theorem abs_two_mul_mul_vecDot_le_param {η w τ : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (hτ : 0 < τ) (ξ ζ : Vec d) :
    |2 * η * w * vecDot (matVecMul A ξ) ζ| ≤
      τ * (η ^ 2 * vecDot ξ (matVecMul A ξ)) + (Λ / τ) * (w ^ 2 * vecNormSq ζ) := by
  have hflux := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA ξ
  have hdotSq := sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A ξ) ζ
  have hE : 0 ≤ vecDot ξ (matVecMul A ξ) := vecDot_matVecMul_self_nonneg hA ξ
  have hΛ : 0 ≤ Λ := hA.Lam_pos.le
  have hfac : 0 ≤ 4 * η ^ 2 * w ^ 2 := by positivity
  have hsq :
      (2 * η * w * vecDot (matVecMul A ξ) ζ) ^ 2 ≤
        (2 * τ * (η ^ 2 * vecDot ξ (matVecMul A ξ))) *
          (2 * (Λ / τ) * (w ^ 2 * vecNormSq ζ)) := by
    calc
      (2 * η * w * vecDot (matVecMul A ξ) ζ) ^ 2 =
          (4 * η ^ 2 * w ^ 2) * vecDot (matVecMul A ξ) ζ ^ 2 := by ring
      _ ≤ (4 * η ^ 2 * w ^ 2) *
          (vecNormSq (matVecMul A ξ) * vecNormSq ζ) :=
        mul_le_mul_of_nonneg_left hdotSq hfac
      _ ≤ (4 * η ^ 2 * w ^ 2) *
          ((Λ * vecDot ξ (matVecMul A ξ)) * vecNormSq ζ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hflux (vecNormSq_nonneg ζ)) hfac
      _ = (2 * τ * (η ^ 2 * vecDot ξ (matVecMul A ξ))) *
          (2 * (Λ / τ) * (w ^ 2 * vecNormSq ζ)) := by
        field_simp
        ring
  have hyoung := abs_le_add_halves_of_sq_le_mul hsq
    (mul_nonneg (mul_nonneg (by norm_num) hτ.le) (mul_nonneg (sq_nonneg η) hE))
    (mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hΛ hτ.le))
      (mul_nonneg (sq_nonneg w) (vecNormSq_nonneg ζ)))
  linarith

/-- **Absorption.** Let `ξ ∈ L²(U)` and `ω ∇η ∈ L²(U)`. If
`c₁ ∫ η² ξ·aξ + c₂ ∫ η ω (aξ·∇η) ≤ 0` with `c₁ > 0`, then
`∫ η² ξ·aξ ≤ (c₂² Λ / c₁²) ∫ ω² |∇η|²`. -/
theorem absorb (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {ξ : Vec d → Vec d} (hξ : MemVectorL2On U ξ) {ω η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hωη : MemVectorL2On U (fun x => ω x • classicalGradient η x))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (htest : c₁ * (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      c₂ * (∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0) :
    ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) ≤
      c₂ ^ 2 * Λ / c₁ ^ 2 *
        ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) := by
  have hηTop : MemLpOn U ⊤ η := memLpOn_top_of_contDiff hη hηc
  have hF := memVectorL2On_matVecMul_of_aemeasurable hU ha hEll hξ
  have hη2 : MemLpOn U ⊤ (fun x => η x ^ 2) := by
    have hsq : (fun x => η x ^ 2) = η * η := by
      funext x
      simp only [Pi.mul_apply, pow_two]
    rw [hsq]
    exact hηTop.mul hηTop
  have hE : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξ i).fun_mul hη2
    simpa only [vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  have hQ : IntegrableOn
      (fun x => ω x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hωη
  have hX : IntegrableOn
      (fun x => η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) U := by
    have hG : MemVectorL2On U (fun x => η x • (ω x • classicalGradient η x)) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hωη i).fun_mul hηTop
    have := integrableOn_vecDot_of_memVectorL2On hF hG
    refine this.congr_fun (fun x _ => ?_) hU
    simp only [vecDot_smul_right]
    ring
  set A := ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) with hAdef
  set Q := ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) with hQdef
  set X := ∫ x in U, η x * ω x *
    vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x) with hXdef
  have hQ0 : 0 ≤ Q := setIntegral_nonneg hU fun x _ =>
    mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
  rcases eq_or_ne c₂ 0 with hc₂ | hc₂
  · rw [hc₂, zero_mul, add_zero] at htest
    have hA0 : A ≤ 0 := by
      by_contra h
      push Not at h
      linarith [mul_pos hc₁ h]
    rw [hc₂]
    simpa using hA0
  · have hc₂abs : 0 < |c₂| := abs_pos.mpr hc₂
    set τ := c₁ / |c₂| with hτdef
    have hτ : 0 < τ := div_pos hc₁ hc₂abs
    have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
      (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun _ hx => hx)
    have hpoint : ∀ᵐ x ∂volumeOn U,
        |η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)| ≤
          (τ / 2) * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
            (Λ / τ / 2) * (ω x ^ 2 * vecNormSq (classicalGradient η x)) := by
      filter_upwards [hmem] with x hx
      have h := abs_two_mul_mul_vecDot_le_param (η := η x) (w := ω x) (hEll x hx) hτ
        (ξ x) (classicalGradient η x)
      have h2 : |2 * η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)| =
          2 * |η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)| := by
        rw [show 2 * η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x) =
          2 * (η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) by ring,
          abs_mul, abs_two]
      rw [h2] at h
      linarith
    have hbound : |X| ≤ (τ / 2) * A + (Λ / τ / 2) * Q := by
      calc |X| ≤ ∫ x in U, |η x * ω x *
            vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)| :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x in U, ((τ / 2) * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
            (Λ / τ / 2) * (ω x ^ 2 * vecNormSq (classicalGradient η x))) :=
          integral_mono_ae hX.abs ((hE.const_mul _).add (hQ.const_mul _)) hpoint
        _ = (τ / 2) * A + (Λ / τ / 2) * Q := by
          rw [integral_add (hE.const_mul _) (hQ.const_mul _), integral_const_mul,
            integral_const_mul]
    have hkey : c₁ * A ≤ |c₂| * ((τ / 2) * A + (Λ / τ / 2) * Q) := by
      have h1 : c₁ * A ≤ -(c₂ * X) := by linarith
      have h2 : -(c₂ * X) ≤ |c₂| * |X| := by
        rw [← abs_mul]
        exact neg_le_abs _
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hbound hc₂abs.le))
    have hτc : |c₂| * (τ / 2) = c₁ / 2 := by
      rw [hτdef]
      field_simp
    have hτΛ : |c₂| * (Λ / τ / 2) = c₂ ^ 2 * Λ / (2 * c₁) := by
      rw [hτdef, ← sq_abs c₂]
      field_simp
    have hkey' : c₁ / 2 * A ≤ c₂ ^ 2 * Λ / (2 * c₁) * Q := by
      have := hkey
      rw [mul_add, ← mul_assoc, ← mul_assoc, hτc, hτΛ] at this
      linarith
    have hfinal : A ≤ (2 / c₁) * (c₂ ^ 2 * Λ / (2 * c₁) * Q) := by
      have h2c : 0 < 2 / c₁ := by positivity
      have := mul_le_mul_of_nonneg_left hkey' h2c.le
      rwa [← mul_assoc, show 2 / c₁ * (c₁ / 2) = 1 by field_simp, one_mul] at this
    calc A ≤ (2 / c₁) * (c₂ ^ 2 * Λ / (2 * c₁) * Q) := hfinal
      _ = c₂ ^ 2 * Λ / c₁ ^ 2 * Q := by
        field_simp

/-- **Energy after absorption.** Under the hypotheses of `absorb`,
`∫ |η ξ + ω ∇η|² ≤ (2 c₂² Λ / c₁² + 2) ∫ ω² |∇η|²`. -/
theorem absorb_energy (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {ξ : Vec d → Vec d} (hξ : MemVectorL2On U ξ) {ω η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hωη : MemVectorL2On U (fun x => ω x • classicalGradient η x))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (htest : c₁ * (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      c₂ * (∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0) :
    ∫ x in U, vecNormSq (η x • ξ x + ω x • classicalGradient η x) ≤
      (2 * (c₂ ^ 2 * Λ / c₁ ^ 2) + 2) *
        ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) := by
  have hA := absorb hU ha hEll hξ hη hηc hωη hc₁ htest
  have hηTop : MemLpOn U ⊤ η := memLpOn_top_of_contDiff hη hηc
  have hF := memVectorL2On_matVecMul_of_aemeasurable hU ha hEll hξ
  have hη2 : MemLpOn U ⊤ (fun x => η x ^ 2) := by
    have hsq : (fun x => η x ^ 2) = η * η := by
      funext x
      simp only [Pi.mul_apply, pow_two]
    rw [hsq]
    exact hηTop.mul hηTop
  have hE : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξ i).fun_mul hη2
    simpa only [vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  have hQ : IntegrableOn
      (fun x => ω x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hωη
  have hA' : MemVectorL2On U (fun x => η x • ξ x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (hξ i).fun_mul hηTop
  have hAB : MemVectorL2On U (fun x => η x • ξ x + ω x • classicalGradient η x) :=
    fun i => (hA' i).add (hωη i)
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun _ hx => hx)
  have hpoint : ∀ᵐ x ∂volumeOn U,
      vecNormSq (η x • ξ x + ω x • classicalGradient η x) ≤
        2 * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
          2 * (ω x ^ 2 * vecNormSq (classicalGradient η x)) := by
    filter_upwards [hmem] with x hx
    have h1 := vecNormSq_add_le (η x • ξ x) (ω x • classicalGradient η x)
    have h2 := vecNormSq_le_vecDot_matVecMul (hEll x hx) (ξ x)
    rw [vecNormSq_smul, vecNormSq_smul] at h1
    have h3 : η x ^ 2 * vecNormSq (ξ x) ≤
        η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    linarith
  have hmono : ∫ x in U, vecNormSq (η x • ξ x + ω x • classicalGradient η x) ≤
      ∫ x in U, (2 * (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
          2 * (ω x ^ 2 * vecNormSq (classicalGradient η x))) :=
    integral_mono_ae (integrableOn_vecNormSq_of_memVectorL2On hAB)
      ((hE.const_mul 2).add (hQ.const_mul 2)) hpoint
  rw [integral_add (hE.const_mul 2) (hQ.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  nlinarith

end DGNM

end PDE
