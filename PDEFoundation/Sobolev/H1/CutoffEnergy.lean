module

public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# Energy of a compactly supported cutoff product

This module records the elementary, but quantitatively important, energy
estimate for `η u`.  Its right-hand side is localized to the prescribed outer
set of the cutoff.  In particular, applications do not need to reprove that
the cutoff-gradient error vanishes outside that set.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U inner outer : Set (Vec d)} {K : ℝ}

/-- The Euclidean energy of the product of an `H¹` representative with a
quantitative cutoff.  The two numerical factors are the literal constants in
`|a + b|² ≤ 2 |a|² + 2 |b|²`; the cutoff-gradient error is localized to
`outer`. -/
theorem setIntegral_vecNormSq_cutoff_product_gradient_le
    (u : H1Function U) (η : QuantitativeSmoothCutoff inner outer K)
    (hU : IsOpenBoundedConvexDomain U) (houter : outer ⊆ U) :
    (∫ x in U,
      vecNormSq (η x • u.grad x +
        u x • classicalGradient η.toFun x)) ≤
      2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
        2 * K ^ 2 * (∫ x in outer, (u x) ^ 2) := by
  have hηTop : MemLpOn U ∞ η.toFun :=
    W1pFunction.cutoff_memLpTop η
  have hDηTop (i : Fin d) :
      MemLpOn U ∞ (fun x => classicalGradient η.toFun x i) :=
    W1pFunction.cutoff_gradient_memLpTop η i
  have hweighted : MemVectorL2On U (fun x => η x • u.grad x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (u.gradMemL2 i).fun_mul hηTop
  have herror : MemVectorL2On U
      (fun x => u x • classicalGradient η.toFun x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      u.memL2.fun_mul (hDηTop i)
  have hsum : MemVectorL2On U
      (fun x => η x • u.grad x +
        u x • classicalGradient η.toFun x) := by
    intro i
    simpa only [Pi.add_apply] using! (hweighted i).add (herror i)
  have hsumInt : IntegrableOn
      (fun x => vecNormSq (η x • u.grad x +
        u x • classicalGradient η.toFun x)) U :=
    integrableOn_vecNormSq_of_memVectorL2On hsum
  have hweightedInt : IntegrableOn
      (fun x => η x ^ 2 * vecNormSq (u.grad x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hweighted
    simpa only [vecNormSq_smul] using hraw
  have herrorInt : IntegrableOn
      (fun x => u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On herror
    simpa only [vecNormSq_smul] using hraw
  have hboundInt : IntegrableOn
      (fun x =>
        2 * (η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (u x ^ 2 * vecNormSq (classicalGradient η.toFun x))) U :=
    hweightedInt.const_mul 2 |>.add (herrorInt.const_mul 2)
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      vecNormSq (η x • u.grad x +
        u x • classicalGradient η.toFun x) ≤
        2 * (η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) :=
    Filter.Eventually.of_forall fun x => by
      have hsum := vecNormSq_add_le (η x • u.grad x)
        (u x • classicalGradient η.toFun x)
      rw [vecNormSq_smul, vecNormSq_smul] at hsum
      nlinarith
  have hsumLe :
      (∫ x in U,
        vecNormSq (η x • u.grad x +
          u x • classicalGradient η.toFun x)) ≤
        ∫ x in U,
          2 * (η x ^ 2 * vecNormSq (u.grad x)) +
            2 * (u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) :=
    integral_mono_ae hsumInt hboundInt hpointwise
  have hsumLeSplit :
      (∫ x in U,
        vecNormSq (η x • u.grad x +
          u x • classicalGradient η.toFun x)) ≤
        2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (∫ x in U,
            u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) := by
    calc
      (∫ x in U,
        vecNormSq (η x • u.grad x +
          u x • classicalGradient η.toFun x)) ≤
          ∫ x in U,
            2 * (η x ^ 2 * vecNormSq (u.grad x)) +
              2 * (u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) :=
        hsumLe
      _ = 2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (∫ x in U,
            u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) := by
        rw [integral_add (hweightedInt.const_mul 2)
          (herrorInt.const_mul 2), integral_const_mul,
          integral_const_mul]
  have herrorRestrict :
      (∫ x in U, u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) =
        ∫ x in outer, u x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet houter fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, pow_two, mul_zero]
  have herrorOuter : IntegrableOn
      (fun x => u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) outer :=
    herrorInt.mono_set houter
  have huSqInt : IntegrableOn (fun x => (u x) ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On u.memL2 u.memL2
  have hKSqOuter : IntegrableOn (fun x => K ^ 2 * (u x) ^ 2) outer :=
    (huSqInt.mono_set houter).const_mul (K ^ 2)
  have herrorLe :
      (∫ x in outer, u x ^ 2 *
        vecNormSq (classicalGradient η.toFun x)) ≤
        K ^ 2 * ∫ x in outer, (u x) ^ 2 := by
    calc
      (∫ x in outer, u x ^ 2 *
        vecNormSq (classicalGradient η.toFun x)) ≤
          ∫ x in outer, K ^ 2 * (u x) ^ 2 := by
        apply integral_mono_ae herrorOuter hKSqOuter
        exact Filter.Eventually.of_forall fun x => by
          have hgradSq :
              vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
            calc
              vecNormSq (classicalGradient η.toFun x) =
                  vecEuclideanNorm (classicalGradient η.toFun x) ^ 2 :=
                (vecEuclideanNorm_sq _).symm
              _ ≤ K ^ 2 :=
                pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
                  (η.gradient_bound x) 2
          calc
            u x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤
                u x ^ 2 * K ^ 2 :=
              mul_le_mul_of_nonneg_left hgradSq (sq_nonneg (u x))
            _ = K ^ 2 * (u x) ^ 2 := by ring
      _ = K ^ 2 * ∫ x in outer, (u x) ^ 2 :=
        integral_const_mul (K ^ 2) _
  calc
    (∫ x in U,
      vecNormSq (η x • u.grad x +
        u x • classicalGradient η.toFun x)) ≤
        2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (∫ x in U,
            u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) :=
      hsumLeSplit
    _ = 2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (∫ x in outer,
            u x ^ 2 * vecNormSq (classicalGradient η.toFun x)) := by
      rw [herrorRestrict]
    _ ≤ 2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
          2 * (K ^ 2 * ∫ x in outer, (u x) ^ 2) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left herrorLe
          (show (0 : ℝ) ≤ 2 by norm_num)) _
    _ = 2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
          2 * K ^ 2 * (∫ x in outer, (u x) ^ 2) := by ring

/-- The cutoff-product energy estimate expressed directly through the chosen
`H¹₀` gradient representative. -/
theorem setIntegral_vecNormSq_mulCutoffToH10_grad_le
    (u : H1Function U) (η : QuantitativeSmoothCutoff inner outer K)
    (hU : IsOpenBoundedConvexDomain U) (houter : outer ⊆ U) :
    (∫ x in U,
      vecNormSq ((u.mulCutoffToH10 hU η houter).toH1Function.grad x)) ≤
      2 * (∫ x in U, η x ^ 2 * vecNormSq (u.grad x)) +
        2 * K ^ 2 * (∫ x in outer, (u x) ^ 2) := by
  rw [mulCutoffToH10_grad]
  exact setIntegral_vecNormSq_cutoff_product_gradient_le u η hU houter

end H1Function

end PDE
