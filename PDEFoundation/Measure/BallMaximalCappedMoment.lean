module

public import PDEFoundation.Measure.BallMaximalTruncatedWeakENN
public import PDEFoundation.Measure.CappedTailMoment

/-! # Finite moments of the actual ball maximal function -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The actual uncentered ball maximal function satisfies the strong moment
estimate at every finite cap, with no prior integrability of the maximal
function. -/
theorem lintegral_rpow_capped_uncenteredBallMaximal_le
    {d : ℕ} (b : Vec d → ℝ) {q : ℝ} (hq : 1 < q)
    (hb : MemLp b (ENNReal.ofReal q) volume) (N : NNReal) :
    (∫⁻ x, ENNReal.ofReal ((cappedENNReal (uncenteredBallMaximal b x) N) ^ q)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q * (3 : ℝ) ^ d * q / (q - 1)) *
        ∫⁻ x, ENNReal.ofReal (|b x| ^ q) := by
  have h := lintegral_rpow_cappedENNReal_le_of_distribution volume b
    hb.aestronglyMeasurable (uncenteredBallMaximal b)
    (measurable_uncenteredBallMaximal b) hq
    (show 0 ≤ 2 * (3 : ℝ) ^ d by positivity)
    (fun t ht => volume_set_lt_uncenteredBallMaximal_le_tail_lintegral b hq hb ht) N
  have hcoeff :
      2 * (3 : ℝ) ^ d * q / (q - 1) * (2 : ℝ) ^ (q - 1) =
        (2 : ℝ) ^ q * (3 : ℝ) ^ d * q / (q - 1) := by
    have hp : (2 : ℝ) ^ q = 2 * (2 : ℝ) ^ (q - 1) := by
      calc
        (2 : ℝ) ^ q = (2 : ℝ) ^ (1 + (q - 1)) := by congr 1; ring
        _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (q - 1) :=
          Real.rpow_add (by norm_num) _ _
        _ = 2 * (2 : ℝ) ^ (q - 1) := by rw [Real.rpow_one]
    rw [hp]
    ring
  rwa [hcoeff] at h

end PDE
