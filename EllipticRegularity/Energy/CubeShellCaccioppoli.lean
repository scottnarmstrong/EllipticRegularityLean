module

public import EllipticRegularity.Energy.SmartCaccioppoli
public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Sobolev.Cutoff.Cube

/-!
# Shell-localized Caccioppoli estimate on cubes

The product cutoff on an arbitrary-dimensional axis cube combines with the
parameterized smart Caccioppoli inequality. With lower ellipticity normalized
to `1`, choosing `τ = sqrt Λ` gives the square-root coefficient on both shell
terms.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- Shell-localized Caccioppoli on a centered cube, with lower ellipticity
normalized to `1`.

The shell is the open cube of half-side `2r` minus the closed cube of half-side
`r`. The cutoff contributes the explicit dimensional gradient constant
`32 * d / r`; no coefficient, domain, solution, or scale enters that constant.
-/
theorem cube_shell_caccioppoli
    {d : ℕ} {Λ : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (k : ℝ) :
    ∫ x in closedCenteredAxisCube x₀ r,
        vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      Real.sqrt Λ *
        (∫ x in centeredAxisCube x₀ (2 * r) \ closedCenteredAxisCube x₀ r,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
      Real.sqrt Λ * ((32 * (d : ℝ)) / r) ^ 2 *
        (∫ x in centeredAxisCube x₀ (2 * r) \ closedCenteredAxisCube x₀ r,
          (u x - k) ^ 2) := by
  have hcenter : x₀ ∈ centeredAxisCube x₀ (2 * r) := by
    exact center_mem_centeredAxisCube x₀ (by positivity)
  have hΛ : 0 < Λ :=
    (hEll.elliptic (houter hcenter)).Lam_pos
  have hsmart := smart_caccioppoli_normalized_energy_sqrt_on_inner
    hU
    (isClosed_closedCenteredAxisCube x₀ r).measurableSet
    (isOpen_centeredAxisCube x₀ (2 * r)).measurableSet
    hEll (by norm_num) hΛ hsol
    (quantitativeCenteredAxisCubeCutoff x₀ hr) houter (k := k)
  simpa only [div_one] using hsmart

end PDE
