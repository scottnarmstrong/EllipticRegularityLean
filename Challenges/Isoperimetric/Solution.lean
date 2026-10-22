module

public import PDEFoundation.FunctionalInequalities.IsoperimetricProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Isoperimetric inequality (Proposition 1.1, inequality part): the repository proof applied to
the statement of `Challenge.lean`. -/
theorem isoperimetric_inequality
    (d : ℕ) (hd : 1 ≤ d) (E : Set (Vec d))
    (hEopen : IsOpen E) (hEbdd : Bornology.IsBounded E) (hEne : E.Nonempty)
    (hE : HasC1Boundary E) :
    ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d) *
        (volume E).toReal ^(((d : ℝ) - 1) / d)) ≤
      (μHE[d - 1] : Measure (HilbertVec d)) (Vec.toHilbertVec '' frontier E) :=
  PDE.IsoperimetricProof.result d hd E hEopen hEbdd hEne hE

end PDE
