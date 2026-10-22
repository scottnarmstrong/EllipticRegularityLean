module

public import PDEFoundation.Analysis.AnalyticOfDerivBound
public import PDEFoundation.Sobolev.Cutoff.Ball

/-!
# Smooth localization of a function on a round ball
-/

@[expose] public section

namespace PDE

open scoped Topology

/-- Multiplying a locally smooth function by a globally smooth function
supported in its domain produces a globally smooth function. -/
theorem contDiff_mul_of_contDiffOn_of_tsupport_subset {d : ℕ}
    {f χ : Vec d → ℝ} {U : Set (Vec d)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hU : IsOpen U)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hnot : x ∉ tsupport χ := fun h => hx (hsupp h)
    have hzero : χ =ᶠ[𝓝 x] (0 : Vec d → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hprod : (fun y => χ y * f y) =ᶠ[𝓝 x] (0 : Vec d → ℝ) := by
      filter_upwards [hzero] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hprod

end PDE
