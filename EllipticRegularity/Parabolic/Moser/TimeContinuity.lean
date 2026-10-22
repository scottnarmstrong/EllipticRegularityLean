/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousOn

public section

/-!
# Upgrading an almost-everywhere bound by continuity

This is the scalar time-continuity step used after a space-time Moser estimate:
if a continuous-in-time pairing obeys an almost-everywhere upper bound on an
open interval, positivity of volume on open sets makes that bound hold at each
time in the interval.
-/

open MeasureTheory Set

namespace PDE.Parabolic.Moser

/-- A continuous function on an open set that is bounded above almost
everywhere with respect to a measure positive on nonempty open sets obeys the
same bound everywhere on that set. -/
theorem continuousOn_le_of_ae_restrict_le
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {s : Set X} (hs : IsOpen s)
    {f : X → ℝ} (hf : ContinuousOn f s) {M : ℝ}
    (hbound : ∀ᵐ x ∂(μ.restrict s), f x ≤ M) :
    ∀ x ∈ s, f x ≤ M := by
  have hbad : μ (s ∩ {x | M < f x}) = 0 := by
    have hzero : μ.restrict s {x | ¬ f x ≤ M} = 0 := by
      exact (ae_iff).1 hbound
    rw [Measure.restrict_apply₀' hs.measurableSet.nullMeasurableSet] at hzero
    simpa only [not_le, inter_comm] using hzero
  have hopen : IsOpen (s ∩ {x | M < f x}) :=
    hf.isOpen_inter_preimage hs isOpen_Ioi
  intro x hx
  by_contra hnot
  have hlt : M < f x := lt_of_not_ge hnot
  have hxBad : x ∈ s ∩ {x | M < f x} := ⟨hx, hlt⟩
  exact hopen.measure_ne_zero μ ⟨x, hxBad⟩ hbad

end PDE.Parabolic.Moser
