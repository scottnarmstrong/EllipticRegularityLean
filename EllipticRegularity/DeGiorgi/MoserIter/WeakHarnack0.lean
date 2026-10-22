module

public import EllipticRegularity.DeGiorgi.MoserIter.WeakHarnackInv
public import EllipticRegularity.DeGiorgi.MoserIter.WeakHarnackSmall

/-!
# Weak Harnack estimates from the one-step estimates

Assembly of Proposition 4.14: the estimate for `inf` (from (H2a)) and the two `L^p`
estimates (from (H2b)), with a common constant.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.DGNMMoser

theorem exists_weakHarnack0_constant_full (d : ℕ) (hd : 3 ≤ d)
    (hInv : WeakHarnackInvOneStepHyp d) (hSmall : WeakHarnackSmallOneStepHyp d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      (∀ p : ℝ, 0 < p →
        ENNReal.ofReal ((Λ * p ^ 2 + 1) ^ (-((d : ℝ) / 2))) *
            (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal ((u.toFun x)⁻¹ ^ p) ∂volume)⁻¹ ≤
          ENNReal.ofReal C *
            (essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p) ∧
      (∀ p q : ℝ, 0 < p → p ≤ q → q < 1 →
        (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ (((d : ℝ) + 2) / 2)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p ∧
        ∀ m : ℕ, 1 ≤ m → p = q * ((d : ℝ) / (d - 2)) ^ (-(m : ℝ)) →
          (eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2)))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
            ENNReal.ofReal (C * (Λ * p ^ 2 / (1 - q) ^ 2 + 1) ^ ((d : ℝ) / 2)) *
              (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_weakHarnack0_inv_constant d hd hInv
  obtain ⟨C₂, hC₂, h₂⟩ := exists_weakHarnack0_small_constant d hd hSmall
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro Λ a hm hell u hpos hsuper
  have hΛ : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 one_pos)).lam_le_Lam
  refine ⟨fun p hp => ?_, fun p q hp hpq hq => ?_⟩
  · exact (h₁ Λ a hm hell u hpos hsuper p hp).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  · obtain ⟨hA, hB⟩ := h₂ Λ a hm hell u hpos hsuper p q hp hpq hq
    have hX : 0 ≤ Λ * p ^ 2 / (1 - q) ^ 2 + 1 := by
      have : 0 ≤ Λ := by linarith
      positivity
    refine ⟨hA.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl),
      fun m hm1 hpm => (hB m hm1 hpm).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)⟩
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hX _)
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hX _)

end PDE.DGNMMoser
