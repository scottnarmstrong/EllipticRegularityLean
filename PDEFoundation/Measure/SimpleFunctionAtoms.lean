module

public import PDEFoundation.Measure.FiniteDisjointAtomLp
public import Mathlib.MeasureTheory.Function.SimpleFunc

@[expose] public section

namespace PDE

open MeasureTheory Set Function
open scoped BigOperators

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The atom of a simple function corresponding to one value in its actual
finite range. -/
def simpleFuncAtomSet (s : SimpleFunc α ℝ) (i : ↥s.range) : Set α :=
  s ⁻¹' {i.1}

/-- The value carried by an atom indexed by the actual range of a simple
function. -/
def simpleFuncAtomValue (s : SimpleFunc α ℝ) (i : ↥s.range) : ℝ :=
  i.1

/-- Every actual range atom of a simple function is measurable. -/
theorem measurableSet_simpleFuncAtomSet (s : SimpleFunc α ℝ) (i : ↥s.range) :
    MeasurableSet (simpleFuncAtomSet s i) :=
  s.measurableSet_fiber i.1

/-- Distinct values in the actual range of a simple function have disjoint
fibers. -/
theorem pairwise_disjoint_simpleFuncAtomSet (s : SimpleFunc α ℝ) :
    Pairwise (Disjoint on simpleFuncAtomSet s) := by
  intro i j hij
  change Disjoint (simpleFuncAtomSet s i) (simpleFuncAtomSet s j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : s x = i.1 := hxi
  have hj : s x = j.1 := hxj
  apply hij
  apply Subtype.ext
  exact hi.symm.trans hj

/-- A real simple function is pointwise exactly the finite disjoint atom sum
over its actual range. -/
theorem finiteDisjointAtomSum_simpleFuncAtomSet (s : SimpleFunc α ℝ) :
    finiteDisjointAtomSum (simpleFuncAtomSet s) (simpleFuncAtomValue s) = s := by
  funext x
  let i : ↥s.range := ⟨s x, s.mem_range_self x⟩
  unfold finiteDisjointAtomSum
  rw [Finset.sum_eq_single i]
  · simp [simpleFuncAtomSet, simpleFuncAtomValue, i]
  · intro j _ hji
    have hj : x ∉ simpleFuncAtomSet s j := by
      intro hxj
      apply hji
      apply Subtype.ext
      exact hxj.symm
    simp [hj]
  · simp

end

end PDE
