module

public import PDEFoundation.Analysis.FiniteExponentialStrip
public import Mathlib.Analysis.Complex.Hadamard

@[expose] public section

open Set Function

namespace PDE

variable {ι : Type*}

/-- A finite exponential sum bounded by the same constant on both edges of the
unit strip is bounded by that constant throughout the closed strip. -/
theorem norm_finiteExponentialSum_le_of_boundary [Fintype ι]
    (c b : ι → ℂ) (a : ι → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hzero : ∀ z : ℂ, z.re = 0 → ‖finiteExponentialSum c b a z‖ ≤ M)
    (hone : ∀ z : ℂ, z.re = 1 → ‖finiteExponentialSum c b a z‖ ≤ M)
    (z : ℂ) (hzZero : 0 ≤ z.re) (hzOne : z.re ≤ 1) :
    ‖finiteExponentialSum c b a z‖ ≤ M := by
  let f : ℂ → ℂ := finiteExponentialSum c b a
  have hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    exact ⟨hzZero, hzOne⟩
  have hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    (finiteExponentialSum_differentiable c b a).diffContOnCl
  have hB : BddAbove ((norm ∘ f) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ i, ‖c i‖ * Real.exp (max (b i).re ((b i).re + a i)), ?_⟩
    rintro y ⟨w, hw, rfl⟩
    apply norm_finiteExponentialSum_le c b a w
    · exact hw.1
    · exact hw.2
  have hthree :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      f hz hd hB
      (fun w hw => hzero w hw)
      (fun w hw => hone w hw)
  have hMPos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  calc
    ‖finiteExponentialSum c b a z‖ ≤ M ^ (1 - z.re) * M ^ z.re := hthree
    _ = M ^ ((1 - z.re) + z.re) := (Real.rpow_add hMPos _ _).symm
    _ = M := by rw [sub_add_cancel, Real.rpow_one]

end PDE
