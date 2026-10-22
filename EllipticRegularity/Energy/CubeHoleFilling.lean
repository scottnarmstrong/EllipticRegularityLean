module

public import EllipticRegularity.Energy.CubeShellCaccioppoli
public import PDEFoundation.Sobolev.Inequalities.CubeShellPoincareMean
public import PDEFoundation.Analysis.HoleFilling
public import PDEFoundation.PDE.CoefficientL2

/-!
# One-step coefficient-energy hole filling on cubes

The coefficient energy on the inner closed cube is bounded by that on the
transition shell. The coefficient is a dimension-only factor times `sqrt Λ`.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The dimension-only factor in the cube-shell hole-filling step. -/
noncomputable def cubeHoleFillingFactor (d : ℕ) : ℝ :=
  1 + (32 * (d : ℝ)) ^ 2 * cubeShellPoincareConst d

/-- The exact one-step coefficient `K` at upper ellipticity `Λ`. -/
noncomputable def cubeHoleFillingK (d : ℕ) (Λ : ℝ) : ℝ :=
  cubeHoleFillingFactor d * Real.sqrt Λ

/-- The dimension-only factor is at least one. -/
theorem cubeHoleFillingFactor_ge_one (d : ℕ) :
    1 ≤ cubeHoleFillingFactor d := by
  have hCP : 0 ≤ cubeShellPoincareConst d := by
    unfold cubeShellPoincareConst
    positivity
  unfold cubeHoleFillingFactor
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hCP)

/-- A positive coefficient bound gives a nonnegative one-step constant. -/
theorem cubeHoleFillingK_nonneg (d : ℕ) (Λ : ℝ) :
    0 ≤ cubeHoleFillingK d Λ := by
  unfold cubeHoleFillingK
  exact mul_nonneg (le_trans zero_le_one (cubeHoleFillingFactor_ge_one d))
    (Real.sqrt_nonneg _)

private theorem closedCube_subset_double_openCube
    {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    closedCenteredAxisCube x₀ r ⊆ centeredAxisCube x₀ (2 * r) := by
  intro x hx i _
  have hxi := hx i (Set.mem_univ i)
  change x₀ i - r ≤ x i ∧ x i ≤ x₀ i + r at hxi
  change x₀ i - 2 * r < x i ∧ x i < x₀ i + 2 * r
  constructor <;> linarith [hxi.1, hxi.2]

/-- Exact integral partition of an open outer cube into a closed inner cube
and its open shell. -/
theorem integral_closedCube_add_cubeShell_eq
    {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {e : Vec d → ℝ} (he : IntegrableOn e (centeredAxisCube x₀ (2 * r))) :
    (∫ x in closedCenteredAxisCube x₀ r, e x) +
        ∫ x in cubeShell x₀ r, e x =
      ∫ x in centeredAxisCube x₀ (2 * r), e x := by
  have hsplit := integral_inter_add_sdiff
    (s := centeredAxisCube x₀ (2 * r))
    (t := closedCenteredAxisCube x₀ r)
    (isClosed_closedCenteredAxisCube x₀ r).measurableSet he
  simpa only [Set.inter_eq_right.mpr
    (closedCube_subset_double_openCube x₀ hr), cubeShell] using hsplit

/-- Shell Poincaré and shell Caccioppoli yield the one-step coefficient-energy
estimate with the exact dimension-only factor. -/
theorem cube_hole_filling_one_step
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∫ x in closedCenteredAxisCube x₀ r,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      cubeHoleFillingK d Λ *
        ∫ x in cubeShell x₀ r,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  let S := cubeShell x₀ r
  let energy : Vec d → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let k := integralAverage S u
  have hSU : S ⊆ U := Set.sdiff_subset.trans houter
  have hSmeas : MeasurableSet S :=
    ((isOpen_centeredAxisCube x₀ (2 * r)).sdiff
      (isClosed_closedCenteredAxisCube x₀ r)).measurableSet
  have hP := poincare_sq_on_cubeShell_average hd u x₀ hr hSU
  have hgradEnergy := setIntegral_vecNormSq_le_coefficientEnergy_div
    hEll u.gradMemL2 hSmeas hSU (by norm_num : (0 : ℝ) < 1)
  have hosc : (∫ x in S, (u x - k) ^ 2) ≤
      cubeShellPoincareConst d * r ^ 2 * ∫ x in S, energy x := by
    calc
      (∫ x in S, (u x - k) ^ 2) ≤
          cubeShellPoincareConst d * r ^ 2 *
            ∫ x in S, vecNormSq (u.grad x) := by
        simpa only [S, k] using hP
      _ ≤ cubeShellPoincareConst d * r ^ 2 *
          ∫ x in S, energy x := by
        simpa only [energy, div_one] using
          mul_le_mul_of_nonneg_left hgradEnergy
            (mul_nonneg
              (le_of_lt (cubeShellPoincareConst_pos hd)) (sq_nonneg r))
  have hC := cube_shell_caccioppoli hU x₀ hr houter hEll hsol k
  have hvalue : Real.sqrt Λ * ((32 * (d : ℝ)) / r) ^ 2 *
      (∫ x in S, (u x - k) ^ 2) ≤
      Real.sqrt Λ * (32 * (d : ℝ)) ^ 2 *
        cubeShellPoincareConst d * ∫ x in S, energy x := by
    calc
      _ ≤ Real.sqrt Λ * ((32 * (d : ℝ)) / r) ^ 2 *
          (cubeShellPoincareConst d * r ^ 2 *
            ∫ x in S, energy x) := by gcongr
      _ = _ := by field_simp [hr.ne']
  calc
    (∫ x in closedCenteredAxisCube x₀ r, energy x) ≤
        Real.sqrt Λ * (∫ x in S, energy x) +
          Real.sqrt Λ * ((32 * (d : ℝ)) / r) ^ 2 *
            ∫ x in S, (u x - k) ^ 2 := by
      simpa only [S, energy, k, cubeShell] using hC
    _ ≤ Real.sqrt Λ * (∫ x in S, energy x) +
          Real.sqrt Λ * (32 * (d : ℝ)) ^ 2 *
            cubeShellPoincareConst d * ∫ x in S, energy x :=
      add_le_add_right hvalue _
    _ = cubeHoleFillingK d Λ * ∫ x in S, energy x := by
      unfold cubeHoleFillingK cubeHoleFillingFactor
      ring

/-- The cube-shell step reorganized into the exact contraction factor
`K/(K+1)` on the outer open cube. -/
theorem cube_hole_filling_contraction
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∫ x in closedCenteredAxisCube x₀ r,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      holeFillingRatio (cubeHoleFillingK d Λ) *
        ∫ x in centeredAxisCube x₀ (2 * r),
          vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  let energy : Vec d → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  have henergy : IntegrableOn energy (centeredAxisCube x₀ (2 * r)) :=
    (integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2).mono_set
      houter
  have hsplit := integral_closedCube_add_cubeShell_eq x₀ hr henergy
  have hfill := cube_hole_filling_one_step hd hU x₀ hr houter hEll hsol
  apply inner_le_holeFillingRatio_mul_outer
    (cubeHoleFillingK_nonneg d Λ)
  dsimp only [energy] at hsplit
  have hEq :
      (∫ x in cubeShell x₀ r,
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) =
      (∫ x in centeredAxisCube x₀ (2 * r),
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) -
      (∫ x in closedCenteredAxisCube x₀ r,
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) := by
    linarith only [hsplit]
  rw [hEq] at hfill
  exact hfill

end PDE
