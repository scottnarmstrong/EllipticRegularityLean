module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceSmooth
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! # Smooth compactly supported tests are dense in whole-space `L²` -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace PDE.Parabolic.LionsRep

/-- Every whole-space `L²` function is approximated in `L²` by a smooth compactly supported
function. -/
theorem exists_smooth_compact_test_approximation {d : ℕ} (ψ : Vec d → ℝ)
    (hψ : MemLp ψ 2 (volume : Measure (Vec d))) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Vec d → ℝ, HasCompactSupport φ ∧ ContDiff ℝ (⊤ : ℕ∞) φ ∧
      eLpNorm (ψ - φ) 2 volume ≤ ENNReal.ofReal ε := by
  exact MeasureTheory.MemLp.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hψ hε

end PDE.Parabolic.LionsRep
