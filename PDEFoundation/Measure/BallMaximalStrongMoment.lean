module

public import PDEFoundation.Measure.BallMaximalCappedMoment
public import PDEFoundation.Measure.ENNRealMomentExhaustion

/-! # Strong moments of the uncentered ball maximal function -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The full strong moment bound follows by exhausting the actual extended
maximal function with finite caps. Its integrability is a consequence of this
bound, never a hypothesis. -/
theorem lintegral_rpow_uncenteredBallMaximal_le
    {d : ℕ} (b : Vec d → ℝ) {q : ℝ} (hq : 1 < q)
    (hb : MemLp b (ENNReal.ofReal q) volume) :
    (∫⁻ x, (uncenteredBallMaximal b x) ^ q) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q * (3 : ℝ) ^ d * q / (q - 1)) *
        ∫⁻ x, ENNReal.ofReal (|b x| ^ q) := by
  exact lintegral_rpow_le_of_cappedENNReal volume (uncenteredBallMaximal b)
    (measurable_uncenteredBallMaximal b) (zero_lt_one.trans hq)
    (fun n => lintegral_rpow_capped_uncenteredBallMaximal_le b hq hb _)

end PDE
