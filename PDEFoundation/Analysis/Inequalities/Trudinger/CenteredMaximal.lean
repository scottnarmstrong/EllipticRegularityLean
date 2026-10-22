module

public import PDEFoundation.Measure.BallMaximalWeak

/-!
# Weak-type maximal inequality for the centered ball maximal function (Lemma 1.15)

The centered maximal function `Mg(x) = sup_{ρ>0} ⨍_{B_ρ(x)} |g|` over open Euclidean balls is
dominated pointwise by the uncentered one, whose weak `(1,1)` estimate with constant `3^d` is
already proved (`volume_set_lt_uncenteredBallMaximal_le`, via a literal compact-cover argument
instead of the Vitali selection). We use the constant `3^d ≤ 5^d`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

/-- The centered maximal function over open Euclidean balls, with extended values. -/
noncomputable def centeredBallMaximal {d : ℕ} (g : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ⨆ ρ : ℝ, ⨆ (_ : 0 < ρ), (volume (euclideanBall x ρ))⁻¹ *
    ∫⁻ y in euclideanBall x ρ, ENNReal.ofReal |g y|

/-- Each real ball average of `|g|` is at most the centered maximal function. -/
theorem ofReal_integralAverage_le_centeredBallMaximal {d : ℕ} {g : Vec d → ℝ}
    (hg : Integrable g volume) (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (integralAverage (euclideanBall x ρ) (fun y => |g y|)) ≤
      centeredBallMaximal g x := by
  rw [ofReal_integralAverage_abs_eq_lintegralAverage g hρ hg.integrableOn]
  exact le_iSup₂_of_le ρ hρ le_rfl

theorem centeredBallMaximal_le_uncentered {d : ℕ} (g : Vec d → ℝ) (x : Vec d) :
    centeredBallMaximal g x ≤ uncenteredBallMaximal g x := by
  refine iSup₂_le fun ρ hρ => ?_
  refine lintegralAverage_le_uncenteredBallMaximal g hρ ?_
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ]
  simpa [vecEuclideanNorm, vecNormSq, vecDot] using hρ

/-- **Weak-type maximal inequality** (Lemma 1.15), with dimensional constant `3^d`. -/
theorem volume_set_lt_centeredBallMaximal_le {d : ℕ} (g : Vec d → ℝ) (t : ℝ) (ht : 0 < t)
    (hg : Integrable g volume) :
    volume {x | ENNReal.ofReal t < centeredBallMaximal g x} ≤
      ENNReal.ofReal ((3 : ℝ) ^ d / t * ∫ x, |g x| ∂volume) :=
  (measure_mono fun x hx => lt_of_lt_of_le hx (centeredBallMaximal_le_uncentered g x)).trans
    (volume_set_lt_uncenteredBallMaximal_le g t ht hg)

end Trudinger
end PDE
