module

public import EllipticRegularity.Energy.SmartCaccioppoli
public import PDEFoundation.Analysis.SquareHoleFilling
public import PDEFoundation.Sobolev.Cutoff.SquareShell
public import PDEFoundation.Sobolev.Inequalities.SquareShellPoincare

/-!
# The two-dimensional square hole-filling step

This module combines the shell-localized Caccioppoli estimate, the explicit
square-shell cutoff, the quantitative shell Poincaré theorem, and integrated
ellipticity. The result has one visible factor `sqrt (Λ / λ)` and a completely
auditable dimension-two numerical constant.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The normalized coefficient energy on the inner square is controlled by
the normalized coefficient energy on the transition shell.

The numerical factor is exactly
`1 + (64 / r)² * (167936 * r²) = 687865857`. Thus the dependence on the
ellipticity ratio is the sharp-order single factor `sqrt (Λ / λ)`. -/
theorem square_hole_filling_one_step
    {lam Lam : ℝ} {U : Set (Vec 2)} {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec 2) {r : ℝ}
    (hr : 0 < r) (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    (∫ x in closedCenteredAxisCube x₀ r,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      687865857 * Real.sqrt (Lam / lam) *
        ((∫ x in dyadicSquareShell x₀ r,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
  let inner := closedCenteredAxisCube x₀ r
  let outer := centeredAxisCube x₀ (2 * r)
  let shell := dyadicSquareShell x₀ r
  let k := integralAverage (dyadicSquareShellTop x₀ r) u
  have hinnerMeas : MeasurableSet inner :=
    (isClosed_closedCenteredAxisCube x₀ r).measurableSet
  have houterMeas : MeasurableSet outer :=
    (isOpen_centeredAxisCube x₀ (2 * r)).measurableSet
  have hshelleq : outer \ inner = shell := rfl
  have hshellU : shell ⊆ U := by simpa only [← hshelleq] using Set.sdiff_subset.trans houter
  have hPoincare := poincare_sq_on_dyadicSquareShell_topAverage u x₀ hr hshellU
  have hgradEnergy :=
    setIntegral_vecNormSq_le_coefficientEnergy_div
      hEll u.gradMemL2 (measurableSet_dyadicSquareShell x₀ r)
      hshellU hlam
  have hosc : ∫ x in shell, (u x - k) ^ 2 ≤
      167936 * r ^ 2 *
        ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
    calc
      ∫ x in shell, (u x - k) ^ 2 ≤
          167936 * r ^ 2 * ∫ x in shell, vecNormSq (u.grad x) := by
        simpa only [shell, k] using hPoincare
      _ ≤ 167936 * r ^ 2 *
          ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
        gcongr
  have hsmart := smart_caccioppoli_normalized_energy_sqrt_on_inner
    hU hinnerMeas houterMeas hEll hlam hLam hsol
    (quantitativeSquareShellCutoff x₀ hr) houter
    (k := k)
  have hvalue : Real.sqrt (Lam / lam) * (64 / r) ^ 2 *
      (∫ x in outer \ inner, (u x - k) ^ 2) ≤
      (687865856 * Real.sqrt (Lam / lam)) *
        ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
    rw [hshelleq]
    calc
      Real.sqrt (Lam / lam) * (64 / r) ^ 2 *
          (∫ x in shell, (u x - k) ^ 2) ≤
          Real.sqrt (Lam / lam) * (64 / r) ^ 2 *
            (167936 * r ^ 2 *
              ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam)) := by
        gcongr
      _ = (687865856 * Real.sqrt (Lam / lam)) *
          ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
        field_simp [hr.ne']
        ring
  rw [hshelleq] at hsmart
  calc
    (∫ x in inner, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
        Real.sqrt (Lam / lam) *
          ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) +
          Real.sqrt (Lam / lam) * (64 / r) ^ 2 *
            (∫ x in shell, (u x - k) ^ 2) := hsmart
    _ ≤ Real.sqrt (Lam / lam) *
          ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) +
          (687865856 * Real.sqrt (Lam / lam)) *
            ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) :=
      add_le_add_right hvalue _
    _ = 687865857 * Real.sqrt (Lam / lam) *
          ((∫ x in shell, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by ring
    _ = 687865857 * Real.sqrt (Lam / lam) *
          ((∫ x in dyadicSquareShell x₀ r,
            vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by rfl

/-- Exact contraction form of `square_hole_filling_one_step`.

The contraction parameter remains literally
`687865857 * sqrt (Λ / λ)`, so the abstract dyadic exponent has order
`sqrt (λ / Λ)` without hiding any ellipticity dependence. -/
theorem square_hole_filling_contraction
    {lam Lam : ℝ} {U : Set (Vec 2)}
    {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec 2) {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    (∫ x in closedCenteredAxisCube x₀ r,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      holeFillingRatio
          (687865857 * Real.sqrt (Lam / lam)) *
        ((∫ x in centeredAxisCube x₀ (2 * r),
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) := by
  let energy : Vec 2 → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let K : ℝ := 687865857 * Real.sqrt (Lam / lam)
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have henergyU : IntegrableOn energy U :=
    integrableOn_coefficientEnergy_of_isEllipticFieldOn
      hEll u.gradMemL2
  have henergyOuter :
      IntegrableOn energy (centeredAxisCube x₀ (2 * r)) :=
    henergyU.mono_set houter
  have hsplitRaw :=
    integral_closedCenteredAxisCube_add_dyadicSquareShell_eq
      x₀ hr henergyOuter
  have hsplit :
      (∫ x in closedCenteredAxisCube x₀ r, energy x) / lam +
          (∫ x in dyadicSquareShell x₀ r, energy x) / lam =
        (∫ x in centeredAxisCube x₀ (2 * r), energy x) / lam := by
    calc
      (∫ x in closedCenteredAxisCube x₀ r, energy x) / lam +
          (∫ x in dyadicSquareShell x₀ r, energy x) / lam =
          ((∫ x in closedCenteredAxisCube x₀ r, energy x) +
            ∫ x in dyadicSquareShell x₀ r, energy x) / lam := by
        ring
      _ = (∫ x in centeredAxisCube x₀ (2 * r), energy x) / lam := by
        rw [hsplitRaw]
  have hfill :
      (∫ x in closedCenteredAxisCube x₀ r, energy x) / lam ≤
        K * ((∫ x in dyadicSquareShell x₀ r, energy x) / lam) := by
    simpa only [energy, K] using
      square_hole_filling_one_step
        hU x₀ hr houter hEll hlam hLam hsol
  apply inner_le_holeFillingRatio_mul_outer hK
  nlinarith [hfill, hsplit]

end PDE
