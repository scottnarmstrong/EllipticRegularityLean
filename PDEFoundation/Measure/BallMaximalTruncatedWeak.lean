module

public import PDEFoundation.Measure.BallMaximalSubadd
public import PDEFoundation.Measure.BallMaximalWeak
public import PDEFoundation.Measure.LpTailIntegrability

/-! # The high-tail weak estimate for `L^q` inputs -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- Truncation at half the level gives the distribution estimate used in the
strong maximal bound. Tail integrability is derived from the actual `L^q`
hypothesis, and the level-set measure is kept extended real. -/
theorem volume_set_lt_uncenteredBallMaximal_le_tail
    {d : ℕ} (b : Vec d → ℝ) {q : ℝ} (hq : 1 < q)
    (hb : MemLp b (ENNReal.ofReal q) volume) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < uncenteredBallMaximal b x} ≤
      ENNReal.ofReal ((2 * (3 : ℝ) ^ d / t) *
        ∫ x, |({y | t / 2 < |b y|}.indicator b) x|) := by
  let s := t / 2
  have hs : 0 < s := div_pos ht (by norm_num)
  let high : Vec d → ℝ := {y | s < |b y|}.indicator b
  let low : Vec d → ℝ := fun y => b y - high y
  have hhigh : Integrable high volume :=
    integrable_indicator_abs_gt_of_memLp b hq hs hb
  have hlow : AEStronglyMeasurable low volume :=
    hb.aestronglyMeasurable.sub hhigh.aestronglyMeasurable
  have hlowBound : ∀ᵐ y ∂volume, |low y| ≤ s := by
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : s < |b y|
    · have hhighValue : high y = b y :=
        Set.indicator_of_mem (show y ∈ {y | s < |b y|} from hy) b
      rw [show low y = b y - high y from rfl, hhighValue, sub_self, abs_zero]
      exact hs.le
    · have hhighValue : high y = 0 :=
        Set.indicator_of_notMem (show y ∉ {y | s < |b y|} from hy) b
      rw [show low y = b y - high y from rfl, hhighValue, sub_zero]
      exact le_of_not_gt hy
  have hsplit : (fun y => low y + high y) = b := by
    funext y
    exact sub_add_cancel _ _
  have hsub : {x | ENNReal.ofReal t < uncenteredBallMaximal b x} ⊆
      {x | ENNReal.ofReal s < uncenteredBallMaximal high x} := by
    intro x hx
    by_contra hnot
    have hcap : uncenteredBallMaximal high x ≤ ENNReal.ofReal s := le_of_not_gt hnot
    have hmax := uncenteredBallMaximal_add_le low high hlow x
    rw [hsplit] at hmax
    have htotal := hmax.trans (add_le_add
      (uncenteredBallMaximal_le_of_ae_abs_le low hlowBound x) hcap)
    have hlevel : ENNReal.ofReal s + ENNReal.ofReal s = ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add hs.le hs.le]
      congr 1
      dsimp only [s]
      ring
    rw [hlevel] at htotal
    exact (not_lt_of_ge htotal) hx
  have hweak := volume_set_lt_uncenteredBallMaximal_le high s hs hhigh
  have hfactor : (3 : ℝ) ^ d / s = 2 * (3 : ℝ) ^ d / t := by
    dsimp only [s]
    field_simp
  exact (measure_mono hsub).trans (by simpa only [hfactor] using hweak)

end PDE
