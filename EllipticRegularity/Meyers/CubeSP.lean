module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.Inequalities.SobolevPoincare
public import PDEFoundation.Measure.NormalizedLp

/-!
# Sobolev--Poincaré on cubes (equation 4.21)

The convex Sobolev--Poincaré inequality (Theorem 1.9)
is taken as an explicit hypothesis `ConvexSobolevPoincareHyp d`, with exactly the type of
`PDE.exists_convexSobolevPoincare_constant d hd`.
Specializing to `p = q = 2d/(d+1)` (so `γ_q = 2`) and the cube `Q` of side `2r`,
whose Euclidean diameter is at most `√d · 2r`, gives the cube inequality with
`S(d) = 2 √d C(d)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

/-- The statement of `PDE.exists_convexSobolevPoincare_constant d hd`, as an explicit
hypothesis. -/
def ConvexSobolevPoincareHyp (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 ≤ p → p < d →
      ∀ (V : Set (Vec d)) (D : ℝ),
        IsOpenBoundedConvexDomain V → V.Nonempty →
        HasEuclideanDiameterLE V D →
        ∀ u : W1pFunction V (ENNReal.ofReal p),
          eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d p))
              (fun x => u.toFun x - integralAverage V u.toFun) ≤
            ENNReal.ofReal (C * (p * ((d : ℝ) - 1) / ((d : ℝ) - p)) * D) *
              euclideanFieldELpMeanNormOn V (ENNReal.ofReal p) u.grad

theorem centeredAxisCube_eq_axisCube {d : ℕ} (z : Vec d) (r : ℝ) :
    centeredAxisCube z r = axisCube (fun i => z i - r) (2 * r) := by
  ext x
  simp only [centeredAxisCube, axisBox, axisCube, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo]
  constructor <;> intro h i <;> obtain ⟨h1, h2⟩ := h i <;> constructor <;> linarith

theorem isOpenBoundedConvexDomain_centeredAxisCube {d : ℕ} (z : Vec d) (r : ℝ) :
    IsOpenBoundedConvexDomain (centeredAxisCube z r) := by
  rw [centeredAxisCube_eq_axisCube]
  exact isOpenBoundedConvexDomain_axisCube _ _

theorem centeredAxisCube_nonempty {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (centeredAxisCube z r).Nonempty := by
  rw [centeredAxisCube_eq_axisCube]
  exact axisCube_nonempty _ (by linarith)

theorem hasEuclideanDiameterLE_centeredAxisCube {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    HasEuclideanDiameterLE (centeredAxisCube z r) (Real.sqrt d * (2 * r)) := by
  rw [centeredAxisCube_eq_axisCube]
  exact hasEuclideanDiameterLE_axisCube _ (by linarith)

/-- Sobolev--Poincaré on axis cubes, with `q = 2d/(d+1)`, `q' = 2d/(d-1)` and the
constant `S(d) = 2 √d C(d)`. -/
theorem cube_sobolevPoincare (d : ℕ) (hd : 2 ≤ d) (hSP : ConvexSobolevPoincareHyp d) :
    ∃ S : ℝ, 0 < S ∧
      ∀ (z : Vec d) (r : ℝ), 0 < r →
      ∀ v : W1pFunction (centeredAxisCube z r)
          (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1))),
        eLpMeanNormOn (centeredAxisCube z r)
            (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1)))
            (fun x => v.toFun x - integralAverage (centeredAxisCube z r) v.toFun) ≤
          ENNReal.ofReal (S * (2 * r)) *
            euclideanFieldELpMeanNormOn (centeredAxisCube z r)
              (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1))) v.grad := by
  obtain ⟨C, hC, hCthm⟩ := hSP
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨2 * C * Real.sqrt d, by positivity, ?_⟩
  intro z r hr v
  have hq1 : 1 ≤ 2 * (d : ℝ) / ((d : ℝ) + 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hqd : 2 * (d : ℝ) / ((d : ℝ) + 1) < d := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have h1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (d : ℝ) + 1 ≠ 0 := by linarith
  have h3 : (d : ℝ) - 2 * (d : ℝ) / ((d : ℝ) + 1) =
      (d : ℝ) * ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
    field_simp; ring
  have hconj : sobolevConjugate d (2 * (d : ℝ) / ((d : ℝ) + 1)) =
      2 * (d : ℝ) / ((d : ℝ) - 1) := by
    unfold sobolevConjugate
    rw [h3]
    field_simp
  have hgamma : 2 * (d : ℝ) / ((d : ℝ) + 1) * ((d : ℝ) - 1) /
      ((d : ℝ) - 2 * (d : ℝ) / ((d : ℝ) + 1)) = 2 := by
    rw [h3]
    field_simp
  have key := hCthm _ hq1 hqd (centeredAxisCube z r) (Real.sqrt d * (2 * r))
    (isOpenBoundedConvexDomain_centeredAxisCube z r) (centeredAxisCube_nonempty z hr)
    (hasEuclideanDiameterLE_centeredAxisCube z hr.le) v
  rw [hconj, hgamma] at key
  refine key.trans (le_of_eq ?_)
  congr 2
  ring

end PDE.MeyersRH
