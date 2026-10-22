module

public import PDEFoundation.PDE.DGNM.ProductTest
public import PDEFoundation.PDE.DGNM.Caccioppoli
public import PDEFoundation.Sobolev.H1.CutoffEnergy
public import EllipticRegularity.DeGiorgi.OneStep.Algebra

/-!
# Energy estimate from a power test function

Abstract form of Step 1 of the Moser one-step estimates.  Given `u`, `w = u ^ σ`,
`v = u ^ (2σ-1)` (as `H¹` functions with the expected gradients on the support of the
cutoff `η`) and the tested inequality `τ · (∫ η² a∇u·∇v + ∫ 2ηv a∇u·∇η) ≤ 0`, we prove
`∫ η² ∇w·a∇w ≤ 4σ²Λ/(2σ-1)² · ∫ w² |∇η|²`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.DGNMOneStep

open MeasureTheory PDE

variable {d : ℕ} {U inner outer : Set (Vec d)} {K Λ : ℝ} {a : CoeffField d}

/-- The cutoff-gradient error term is integrable and localized to the outer set. -/
theorem cutoffError_le (hU : IsOpenBoundedConvexDomain U) (w : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    IntegrableOn (fun x => w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) U ∧
      (∫ x in U, w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) ≤
        K ^ 2 * ∫ x in outer, w x ^ 2 := by
  let G : Vec d → Vec d := fun x => w x • classicalGradient η.toFun x
  have hDηTop (i : Fin d) : MemLpOn U ∞ (fun x => classicalGradient η.toFun x i) :=
    W1pFunction.cutoff_gradient_memLpTop η i
  have hG : MemVectorL2On U G := by
    intro i
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using w.memL2.fun_mul (hDηTop i)
  have hgradientInt : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hG
    simpa only [G, vecNormSq_smul] using hraw
  refine ⟨hgradientInt, ?_⟩
  have hwSqInt : IntegrableOn (fun x => w x ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On w.memL2 w.memL2
  have hgradientRestrict :
      (∫ x in U, w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) =
        ∫ x in outer, w x ^ 2 * vecNormSq (classicalGradient η.toFun x) := by
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet houter fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, pow_two, mul_zero]
  have hgradientOuter : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) outer :=
    hgradientInt.mono_set houter
  have hKSqOuter : IntegrableOn (fun x => K ^ 2 * w x ^ 2) outer :=
    (hwSqInt.mono_set houter).const_mul (K ^ 2)
  rw [hgradientRestrict]
  calc
    (∫ x in outer, w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) ≤
        ∫ x in outer, K ^ 2 * w x ^ 2 := by
      apply integral_mono_ae hgradientOuter hKSqOuter
      exact Filter.Eventually.of_forall fun x => by
        have hgradSq : vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
          calc
            vecNormSq (classicalGradient η.toFun x) =
                vecEuclideanNorm (classicalGradient η.toFun x) ^ 2 :=
              (vecEuclideanNorm_sq _).symm
            _ ≤ K ^ 2 :=
              pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) (η.gradient_bound x) 2
        calc
          w x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤ w x ^ 2 * K ^ 2 :=
            mul_le_mul_of_nonneg_left hgradSq (sq_nonneg (w x))
          _ = K ^ 2 * w x ^ 2 := by ring
    _ = K ^ 2 * ∫ x in outer, w x ^ 2 := integral_const_mul (K ^ 2) _

/-- Pointwise algebra: the flux terms of the tested inequality in terms of `w = u ^ σ`. -/
theorem flux_terms_eq {A : Mat d} {σ : ℝ} (hσ : σ ≠ 0) {t η : ℝ} (ht : 0 < t)
    (gu gη : Vec d) :
    η ^ 2 * vecDot (matVecMul A gu) (((2 * σ - 1) * t ^ (2 * σ - 2)) • gu) =
        (2 * σ - 1) / σ ^ 2 *
          (η ^ 2 * vecDot ((σ * t ^ (σ - 1)) • gu)
            (matVecMul A ((σ * t ^ (σ - 1)) • gu))) ∧
      2 * η * t ^ (2 * σ - 1) * vecDot (matVecMul A gu) gη =
        1 / σ * (2 * η * t ^ σ *
          vecDot (matVecMul A ((σ * t ^ (σ - 1)) • gu)) gη) := by
  have hsq : (t ^ (σ - 1)) ^ 2 = t ^ (2 * σ - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1; push_cast; ring
  have hmul : t ^ (2 * σ - 1) = t ^ σ * t ^ (σ - 1) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  constructor
  · rw [DGNM.vecDot_smul_right, DGNM.vecDot_smul_left, DGNM.matVecMul_smul,
      DGNM.vecDot_smul_right, vecDot_comm gu]
    rw [← hsq]
    field_simp
  · rw [DGNM.matVecMul_smul, DGNM.vecDot_smul_left, hmul]
    field_simp

/-- Energy estimate from the power test function. -/
theorem energy_of_test (hU : IsOpenBoundedConvexDomain U)
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) (hΛ : 0 ≤ Λ)
    (u w v : H1Function U) {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ^ 2 = 1)
    (hpos : 0 < τ * (2 * σ - 1))
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U)
    (hreg : ∀ᵐ x ∂volumeOn U, η x ≠ 0 →
      0 < u x ∧ w x = u x ^ σ ∧ w.grad x = (σ * u x ^ (σ - 1)) • u.grad x ∧
        v x = u x ^ (2 * σ - 1) ∧
        v.grad x = ((2 * σ - 1) * u x ^ (2 * σ - 2)) • u.grad x)
    (htest :
      IntegrableOn (fun x => η x ^ 2 *
        vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) U ∧
      IntegrableOn (fun x => 2 * η x * v x *
        vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η.toFun x)) U ∧
      τ * ((∫ x in U, η x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (v.grad x)) +
        ∫ x in U, 2 * η x * v x *
          vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η.toFun x)) ≤ 0) :
    IntegrableOn (fun x => η x ^ 2 * vecDot (w.grad x) (matVecMul (a x) (w.grad x))) U ∧
    (∫ x in U, η x ^ 2 * vecDot (w.grad x) (matVecMul (a x) (w.grad x))) ≤
      4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 * (K ^ 2 * ∫ x in outer, w x ^ 2) := by
  obtain ⟨hint1, hint2, hsign⟩ := htest
  have hne : 2 * σ - 1 ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  have hne2 : σ * 2 - 1 ≠ 0 := by
    intro h; apply hne; linarith
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; norm_num at hτ
  set J1 : Vec d → ℝ := fun x => η x ^ 2 * vecDot (w.grad x) (matVecMul (a x) (w.grad x)) with hJ1
  set J2 : Vec d → ℝ := fun x => 2 * η x * w x *
    vecDot (matVecMul (a x) (w.grad x)) (classicalGradient η.toFun x) with hJ2
  set F1 : Vec d → ℝ := fun x => η x ^ 2 *
    vecDot (matVecMul (a x) (u.grad x)) (v.grad x) with hF1
  set F2 : Vec d → ℝ := fun x => 2 * η x * v x *
    vecDot (matVecMul (a x) (u.grad x)) (classicalGradient η.toFun x) with hF2
  have hae : ∀ᵐ x ∂volumeOn U, F1 x = (2 * σ - 1) / σ ^ 2 * J1 x ∧ F2 x = 1 / σ * J2 x := by
    filter_upwards [hreg] with x hx
    by_cases hηx : η x = 0
    · simp [hF1, hF2, hJ1, hJ2, hηx]
    · obtain ⟨hu, hw, hgw, hv, hgv⟩ := hx hηx
      have := flux_terms_eq (A := a x) hσ hu (η := η x) (u.grad x) (classicalGradient η.toFun x)
      simp only [hF1, hF2, hJ1, hJ2, hw, hgw, hv, hgv]
      exact this
  have hJ1int : Integrable J1 (volumeOn U) := by
    have h := hint1.const_mul (σ ^ 2 / (2 * σ - 1))
    refine h.congr ?_
    filter_upwards [hae] with x hx
    rw [hx.1]
    field_simp [hne2]
  have hJ2int : Integrable J2 (volumeOn U) := by
    have h := hint2.const_mul σ
    refine h.congr ?_
    filter_upwards [hae] with x hx
    rw [hx.2]
    field_simp
  refine ⟨hJ1int, ?_⟩
  have hI1 : (∫ x in U, F1 x) = (2 * σ - 1) / σ ^ 2 * ∫ x in U, J1 x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards [hae] with x hx using hx.1)
  have hI2 : (∫ x in U, F2 x) = 1 / σ * ∫ x in U, J2 x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards [hae] with x hx using hx.2)
  obtain ⟨hWint, hWle⟩ := cutoffError_le hU w η houter
  -- the absorption inequality
  have hy : ∀ ε : ℝ, 0 < ε → |∫ x in U, J2 x| ≤
      ε * (∫ x in U, J1 x) + Λ / ε *
        ∫ x in U, w x ^ 2 * vecNormSq (classicalGradient η.toFun x) := by
    intro ε hε
    have hbd : Integrable (fun x => ε * J1 x + Λ / ε *
        (w x ^ 2 * vecNormSq (classicalGradient η.toFun x))) (volumeOn U) :=
      (hJ1int.const_mul ε).add (hWint.const_mul (Λ / ε))
    have hpt : ∀ᵐ x ∂volumeOn U, ‖J2 x‖ ≤ ε * J1 x + Λ / ε *
        (w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [Real.norm_eq_abs]
      exact abs_two_mul_mul_vecDot_le_eps (hEll x hx) (w.grad x)
        (classicalGradient η.toFun x) hε
    have := norm_integral_le_of_norm_le hbd hpt
    rw [Real.norm_eq_abs, integral_add (hJ1int.const_mul ε) (hWint.const_mul (Λ / ε)),
      integral_const_mul, integral_const_mul] at this
    exact this
  have hτ' : τ * (2 * σ - 1) / σ ^ 2 * (∫ x in U, J1 x) + τ / σ * (∫ x in U, J2 x) ≤ 0 := by
    have : τ * ((∫ x in U, F1 x) + ∫ x in U, F2 x) =
        τ * (2 * σ - 1) / σ ^ 2 * (∫ x in U, J1 x) + τ / σ * (∫ x in U, J2 x) := by
      rw [hI1, hI2]; ring
    rw [← this]; exact hsign
  have hc₁ : 0 < τ * (2 * σ - 1) / σ ^ 2 := by positivity
  have hc₂ : τ / σ ≠ 0 := div_ne_zero hτ0 hσ
  have habs := absorb (c₁ := τ * (2 * σ - 1) / σ ^ 2) (c₂ := τ / σ) (Λ := Λ)
    (W := ∫ x in U, w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) hc₁ hc₂ hτ' hy
  have hcoef : 4 * (τ / σ) ^ 2 * Λ / (τ * (2 * σ - 1) / σ ^ 2) ^ 2 =
      4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 := by
    have hτ4 : τ ^ 4 = 1 := by nlinarith [hτ]
    have e1 : (τ / σ) ^ 2 = 1 / σ ^ 2 := by rw [div_pow, hτ]
    have e2 : (τ * (2 * σ - 1) / σ ^ 2) ^ 2 = (2 * σ - 1) ^ 2 / σ ^ 4 := by
      rw [div_pow, mul_pow, hτ]; ring
    rw [e1, e2]
    field_simp
  rw [hcoef] at habs
  have hcoefnn : 0 ≤ 4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 := by positivity
  calc (∫ x in U, J1 x) ≤ 4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 *
        ∫ x in U, w x ^ 2 * vecNormSq (classicalGradient η.toFun x) := habs
    _ ≤ 4 * σ ^ 2 * Λ / (2 * σ - 1) ^ 2 * (K ^ 2 * ∫ x in outer, w x ^ 2) :=
        mul_le_mul_of_nonneg_left hWle hcoefnn

end PDE.DGNMOneStep
