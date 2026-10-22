module

public import EllipticRegularity.Energy.SquareHoleFilling
public import PDEFoundation.Measure.AxisBoxVolume

/-!
# Dyadic decay from two-dimensional square hole filling

This module iterates the exact one-step square hole-filling contraction on
the radii `R / 2 ^ n`. It then converts the exact geometric decay into a
dyadic power law and records the sharp ellipticity order of the exponent.
-/

@[expose] public section

namespace PDE

open MeasureTheory

private theorem dyadicRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (2 : ℝ) ^ n :=
  div_pos hR (pow_pos (by norm_num) n)

private theorem two_mul_dyadicRadius_succ (R : ℝ) (n : ℕ) :
    2 * (R / (2 : ℝ) ^ (n + 1)) = R / (2 : ℝ) ^ n := by
  rw [pow_succ]
  field_simp

private theorem dyadicRadius_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    R / (2 : ℝ) ^ n ≤ R := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpow_pos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  apply (div_le_iff₀ hpow_pos).2
  nlinarith

/-- The normalized coefficient energy on dyadically shrinking open squares
decays by the exact iterated hole-filling ratio. -/
theorem square_hole_filling_iterate
    {lam Lam : ℝ} {U : Set (Vec 2)}
    {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec 2) {R : ℝ}
    (hR : 0 < R)
    (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) (n : ℕ) :
    (∫ x in centeredAxisCube x₀ (R / (2 : ℝ) ^ n),
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      holeFillingRatio
          (687865857 * Real.sqrt (Lam / lam)) ^ n *
        ((∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
  let energy : Vec 2 → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let E : ℕ → ℝ := fun m =>
    (∫ x in centeredAxisCube x₀ (R / (2 : ℝ) ^ m), energy x) / lam
  let K : ℝ := 687865857 * Real.sqrt (Lam / lam)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hstep : ∀ m, E (m + 1) ≤ holeFillingRatio K * E m := by
    intro m
    have hrm : 0 < R / (2 : ℝ) ^ (m + 1) :=
      dyadicRadius_pos hR (m + 1)
    have hrmR : R / (2 : ℝ) ^ m ≤ R :=
      dyadicRadius_le hR.le m
    have houterm :
        centeredAxisCube x₀
            (2 * (R / (2 : ℝ) ^ (m + 1))) ⊆ U := by
      rw [two_mul_dyadicRadius_succ]
      exact (centeredAxisCube_mono x₀ hrmR).trans houter
    have hone :=
      square_hole_filling_contraction
        hU x₀ hrm houterm hEll hlam hLam hsol
    have hboundary :
        (∫ x in centeredAxisCube x₀ (R / (2 : ℝ) ^ (m + 1)),
            energy x) =
          ∫ x in closedCenteredAxisCube x₀ (R / (2 : ℝ) ^ (m + 1)),
            energy x :=
      setIntegral_congr_set
        (centeredAxisCube_ae_eq_closedCenteredAxisCube
          x₀ (R / (2 : ℝ) ^ (m + 1)))
    dsimp only [E]
    rw [hboundary]
    simpa only [energy, K, two_mul_dyadicRadius_succ] using hone
  have hiterate :=
    iterate_contraction (holeFillingRatio_nonneg hK) hstep n
  simpa only [E, energy, K, pow_zero, div_one] using hiterate

/-- Explicit dyadic power-law decay of the normalized coefficient energy.

The exponent is literally
`1 / (687865857 * sqrt (Λ / λ) + 1)`; no dependence is hidden. -/
theorem square_hole_filling_dyadic_decay
    {lam Lam : ℝ} {U : Set (Vec 2)}
    {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec 2) {R : ℝ}
    (hR : 0 < R)
    (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) (n : ℕ) :
    (∫ x in centeredAxisCube x₀ (R / (2 : ℝ) ^ n),
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      (2 : ℝ) ^
          (-holeFillingDyadicExponent
            (687865857 * Real.sqrt (Lam / lam)) * (n : ℝ)) *
        ((∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
  let energy : Vec 2 → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let K : ℝ := 687865857 * Real.sqrt (Lam / lam)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hE0 :
      0 ≤ (∫ x in centeredAxisCube x₀ R, energy x) / lam := by
    apply div_nonneg
    · apply integral_nonneg_of_ae
      filter_upwards [
          ae_restrict_mem
            (isOpen_centeredAxisCube x₀ R).measurableSet] with x hx
      exact
        (mul_nonneg hlam.le (vecNormSq_nonneg (u.grad x))).trans
          ((hEll.elliptic (houter hx)).coercive (u.grad x))
    · exact hlam.le
  have hiter :=
    square_hole_filling_iterate
      hU x₀ hR houter hEll hlam hLam hsol n
  calc
    (∫ x in centeredAxisCube x₀ (R / (2 : ℝ) ^ n),
        energy x) / lam ≤
        holeFillingRatio K ^ n *
          ((∫ x in centeredAxisCube x₀ R, energy x) / lam) := by
      simpa only [energy, K] using hiter
    _ ≤ (2 : ℝ) ^
          (-holeFillingDyadicExponent K * (n : ℝ)) *
          ((∫ x in centeredAxisCube x₀ R, energy x) / lam) :=
      mul_le_mul_of_nonneg_right
        (holeFillingRatio_pow_le_dyadicPower hK n) hE0
    _ = (2 : ℝ) ^
          (-holeFillingDyadicExponent
            (687865857 * Real.sqrt (Lam / lam)) * (n : ℝ)) *
        ((∫ x in centeredAxisCube x₀ R,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
      rfl

/-- The explicit dyadic exponent has the sharp ellipticity order
`sqrt (λ / Λ)`, up to the displayed numerical factor. -/
theorem square_hole_filling_dyadicExponent_lowerBound
    {lam Lam R : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    (x₀ : Vec 2) (hR : 0 < R)
    (houter : centeredAxisCube x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Real.sqrt (lam / Lam) / (2 * 687865857) ≤
      holeFillingDyadicExponent
        (687865857 * Real.sqrt (Lam / lam)) := by
  have hxU := houter (center_mem_centeredAxisCube x₀ hR)
  have hA := hEll.elliptic hxU
  have hratio : 1 ≤ Lam / lam :=
    (one_le_div₀ hA.lam_pos).2 hA.lam_le_Lam
  have hsqrtSq : Real.sqrt (Lam / lam) ^ 2 = Lam / lam :=
    Real.sq_sqrt (by linarith)
  have hsqrt : 1 ≤ Real.sqrt (Lam / lam) := by
    have hsqrtNonneg : 0 ≤ Real.sqrt (Lam / lam) :=
      Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt (Lam / lam) - 1)]
  have hlower :=
    holeFillingDyadicExponent_mul_sqrt_lowerBound
      (C := (687865857 : ℝ)) (κ := Lam / lam) (by nlinarith)
  have hlamLam : 0 < lam / Lam := div_pos hA.lam_pos hA.Lam_pos
  have hLamlam : 0 < Lam / lam := div_pos hA.Lam_pos hA.lam_pos
  have hsquareOne :
      (Real.sqrt (lam / Lam) * Real.sqrt (Lam / lam)) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hlamLam.le, Real.sq_sqrt hLamlam.le]
    field_simp [hA.lam_pos.ne', hA.Lam_pos.ne']
  have hproductNonneg :
      0 ≤ Real.sqrt (lam / Lam) * Real.sqrt (Lam / lam) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hproduct :
      Real.sqrt (lam / Lam) * Real.sqrt (Lam / lam) = 1 := by
    nlinarith [hsquareOne]
  calc
    Real.sqrt (lam / Lam) / (2 * 687865857) =
        1 / (2 * 687865857 * Real.sqrt (Lam / lam)) := by
      field_simp [show Real.sqrt (Lam / lam) ≠ 0 by positivity]
      nlinarith
    _ ≤ holeFillingDyadicExponent
          (687865857 * Real.sqrt (Lam / lam)) := hlower

end PDE
