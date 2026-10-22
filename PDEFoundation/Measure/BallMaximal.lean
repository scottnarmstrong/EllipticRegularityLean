module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # The uncentered maximal function over round Euclidean balls -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- The uncentered ball maximal function, with extended nonnegative values so
that an unbounded supremum retains its mathematical meaning. -/
noncomputable def uncenteredBallMaximal {d : ℕ} (b : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ⨆ z : Vec d, ⨆ R : ℝ, ⨆ (_hR : 0 < R), ⨆ (_hx : x ∈ euclideanBall z R),
    (volume (euclideanBall z R))⁻¹ *
      ∫⁻ y in euclideanBall z R, ENNReal.ofReal |b y|

/-- Every positive-radius ball containing the point contributes its literal
average of the absolute value to the maximal function. -/
theorem lintegralAverage_le_uncenteredBallMaximal {d : ℕ}
    (b : Vec d → ℝ) {x z : Vec d} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ euclideanBall z R) :
    (volume (euclideanBall z R))⁻¹ *
      (∫⁻ y in euclideanBall z R, ENNReal.ofReal |b y|) ≤ uncenteredBallMaximal b x :=
  le_iSup_of_le z (le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le hx le_rfl)))

/-- Strict superlevel sets are exactly unions of the balls whose averages
exceed the threshold. -/
theorem set_lt_uncenteredBallMaximal {d : ℕ} (b : Vec d → ℝ) (t : ℝ≥0∞) :
    {x | t < uncenteredBallMaximal b x} =
      ⋃ z : Vec d, ⋃ R : ℝ, ⋃ (_hR : 0 < R),
        ⋃ (_havg : t < (volume (euclideanBall z R))⁻¹ *
          ∫⁻ y in euclideanBall z R, ENNReal.ofReal |b y|), euclideanBall z R := by
  ext x
  simp only [uncenteredBallMaximal, mem_ofPred_eq, lt_iSup_iff, mem_iUnion]
  constructor
  · rintro ⟨z, R, hR, hx, havg⟩
    exact ⟨z, R, hR, havg, hx⟩
  · rintro ⟨z, R, hR, havg, hx⟩
    exact ⟨z, R, hR, hx, havg⟩

/-- The literal uncentered supremum is lower semicontinuous because every
strict superlevel set is a union of open round balls. -/
theorem lowerSemicontinuous_uncenteredBallMaximal {d : ℕ} (b : Vec d → ℝ) :
    LowerSemicontinuous (uncenteredBallMaximal b) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.2
  intro t
  change IsOpen {x | t < uncenteredBallMaximal b x}
  rw [set_lt_uncenteredBallMaximal]
  exact isOpen_iUnion fun z => isOpen_iUnion fun R =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_euclideanBall z R

theorem measurable_uncenteredBallMaximal {d : ℕ} (b : Vec d → ℝ) :
    Measurable (uncenteredBallMaximal b) :=
  (lowerSemicontinuous_uncenteredBallMaximal b).measurable

/-- The quadratic maximal function of a vector field uses its Euclidean
quadratic magnitude and the nonnegative extended square root. -/
noncomputable def quadraticBallMaximal {d : ℕ} (F : Vec d → Vec d) (x : Vec d) : ℝ≥0∞ :=
  (uncenteredBallMaximal (fun y => vecNormSq (F y)) x) ^ (1 / 2 : ℝ)

end PDE
