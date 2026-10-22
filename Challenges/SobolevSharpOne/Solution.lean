module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOneProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- Sharp Sobolev inequality for `p = 1` (Proposition 1.4):
`‖u‖_{L^{d/(d-1)}(ℝ^d)} ≤ d⁻¹ |B₁|^{-1/d} ‖∇u‖_{L¹(ℝ^d)}`.  The exponent `d/(d-1)` is taken in
`[1,∞]`, so `d = 1` reads `‖u‖_∞ ≤ ½ ‖u'‖_{L¹}`. -/
theorem sobolev_inequality_sharp_p_one
    (d : ℕ) (hd : 1 ≤ d) (u : W1pFunction (Set.univ : Set (Vec d)) 1) :
    eLpNorm u.toFun ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤
      ENNReal.ofReal (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 1 volume :=
  PDE.SobolevSharpOneProof.result d hd u

end PDE
