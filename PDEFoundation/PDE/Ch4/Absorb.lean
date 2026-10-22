module

public import PDEFoundation.PDE.Ch4.SqTest
public import PDEFoundation.PDE.DGNM.Absorb

/-!
# The absorption step with Lipschitz cutoffs

Open-set version of `PDE.DGNM.absorb` and `absorb_energy`: the cutoff `η` is only required to be
continuous and bounded (the compact support enters through the other hypotheses `hωη`).
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE.Ch4Infra

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}

/-- **Absorption.** Let `ξ ∈ L²(U)` and `ω ∇η ∈ L²(U)`. If
`c₁ ∫ η² ξ·aξ + c₂ ∫ η ω (aξ·∇η) ≤ 0` with `c₁ > 0`, then
`∫ η² ξ·aξ ≤ (c₂² Λ / c₁²) ∫ ω² |∇η|²`. -/
theorem absorb_open (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {ξ : Vec d → Vec d} (hξ : MemVectorL2On U ξ) {ω η : Vec d → ℝ}
    {M : ℝ} (hη : Continuous η) (hM : ∀ x, |η x| ≤ M)
    (hωη : MemVectorL2On U (fun x => ω x • classicalGradient η x))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (htest : c₁ * (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      c₂ * (∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0) :
    ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) ≤
      c₂ ^ 2 * Λ / c₁ ^ 2 *
        ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) := by
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU ha hEll hξ
  have hE : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using
        memL2On_mul_bounded (hξ i) (by fun_prop : Continuous fun x => η x ^ 2) (abs_sq_le hM)
    simpa only [DGNM.vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  have hQ : IntegrableOn
      (fun x => ω x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hωη
  have hX : IntegrableOn
      (fun x => η x * ω x * vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) U := by
    have hG : MemVectorL2On U (fun x => η x • (ω x • classicalGradient η x)) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hωη i) hη hM
    have := integrableOn_vecDot_of_memVectorL2On hF hG
    refine this.congr_fun (fun x _ => ?_) hU
    simp only [DGNM.vecDot_smul_right]
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
      have h := DGNM.abs_two_mul_mul_vecDot_le_param (η := η x) (w := ω x) (hEll x hx) hτ
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
theorem absorb_energy_open (hU : MeasurableSet U)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x))
    {ξ : Vec d → Vec d} (hξ : MemVectorL2On U ξ) {ω η : Vec d → ℝ}
    {M : ℝ} (hη : Continuous η) (hM : ∀ x, |η x| ≤ M)
    (hωη : MemVectorL2On U (fun x => ω x • classicalGradient η x))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (htest : c₁ * (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
      c₂ * (∫ x in U, η x * ω x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η x)) ≤ 0) :
    ∫ x in U, vecNormSq (η x • ξ x + ω x • classicalGradient η x) ≤
      (2 * (c₂ ^ 2 * Λ / c₁ ^ 2) + 2) *
        ∫ x in U, ω x ^ 2 * vecNormSq (classicalGradient η x) := by
  have hA := absorb_open hU ha hEll hξ hη hM hωη hc₁ htest
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hU ha hEll hξ
  have hE : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hC : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using
        memL2On_mul_bounded (hξ i) (by fun_prop : Continuous fun x => η x ^ 2) (abs_sq_le hM)
    simpa only [DGNM.vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  have hQ : IntegrableOn
      (fun x => ω x ^ 2 * vecNormSq (classicalGradient η x)) U := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hωη
  have hA' : MemVectorL2On U (fun x => η x • ξ x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using memL2On_mul_bounded (hξ i) hη hM
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
    have h2 := DGNM.vecNormSq_le_vecDot_matVecMul (hEll x hx) (ξ x)
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


end PDE.Ch4Infra
