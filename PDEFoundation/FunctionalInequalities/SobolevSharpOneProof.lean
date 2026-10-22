module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.DimOne
public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.Assembly

/-!
# Proof of `PDE.sobolev_inequality_sharp_p_one`

`PDE.SobolevSharpOneProof.result` is the sharp `p = 1` Sobolev inequality
`‖u‖_{L^{d/(d-1)}} ≤ d⁻¹ |B₁|^{-1/d} ‖∇u‖_{L¹}`, assembled from the `d = 1` case and the
`d ≥ 2` case (layer-cake Minkowski, smooth layer bound, density reduction).
-/

@[expose] public section

namespace PDE.SobolevSharpOneProof

open MeasureTheory
open scoped ENNReal

theorem result (d : ℕ) (hd : 1 ≤ d) (u : W1pFunction (Set.univ : Set (Vec d)) 1) :
    eLpNorm u.toFun ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤
      ENNReal.ofReal (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 1 volume := by
  rcases Nat.eq_or_lt_of_le hd with h | h
  · exact SobolevSharp.sobolev_sharp_one_of_dim_one d h.symm u
  · exact SobolevSharp.sobolev_sharp_one_of_two_le d h u

end PDE.SobolevSharpOneProof
