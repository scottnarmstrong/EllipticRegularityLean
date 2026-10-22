module

public import PDEFoundation.Geometry.FirstDyadicStop

/-! # The literal dyadic maximal function on a box -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

/-- The extended absolute average on a literal dyadic descendant. -/
noncomputable def dyadicBoxAverage {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) : ℝ≥0∞ :=
  (volume (dyadicDescendant I p : Set (Vec d)))⁻¹ *
    ∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal |b x|

/-- The dyadic maximal function on a root box, extended by zero off that
box. All generations and all containing literal descendants are used. -/
noncomputable def dyadicBoxMaximal {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ⨆ p : List (Set (Fin d)),
    ⨆ (_ : x ∈ (dyadicDescendant I p : Set (Vec d))), dyadicBoxAverage I b p

theorem dyadicBoxAverage_le_dyadicBoxMaximal {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) (p : List (Set (Fin d))) {x : Vec d}
    (hx : x ∈ (dyadicDescendant I p : Set (Vec d))) :
    dyadicBoxAverage I b p ≤ dyadicBoxMaximal I b x := by
  exact le_iSup_of_le p (le_iSup_of_le hx le_rfl)

/-- Off the root carrier there are no admissible descendants. -/
theorem dyadicBoxMaximal_eq_zero_of_notMem {d : ℕ} (I : Box (Fin d))
    (b : Vec d → ℝ) {x : Vec d} (hx : x ∉ (I : Set (Vec d))) :
    dyadicBoxMaximal I b x = 0 := by
  apply le_antisymm _ (zero_le)
  apply iSup_le
  intro p
  apply iSup_le
  intro hxp
  exact (hx (dyadicDescendant_le I p hxp)).elim

/-- Every strict maximal superlevel is covered exactly by its first stopping
descendants. Disjointness follows separately from first-prefix selection. -/
theorem set_lt_dyadicBoxMaximal_eq_firstStops {d : ℕ}
    (I : Box (Fin d)) (b : Vec d → ℝ) (t : ℝ≥0∞) :
    {x | t < dyadicBoxMaximal I b x} =
      ⋃ p : List (Set (Fin d)),
        ⋃ (_ : IsFirstPrefixStop (fun q => t < dyadicBoxAverage I b q) p),
          (dyadicDescendant I p : Set (Vec d)) := by
  ext x
  constructor
  · intro hx
    change t < dyadicBoxMaximal I b x at hx
    unfold dyadicBoxMaximal at hx
    obtain ⟨p, hp⟩ := lt_iSup_iff.mp hx
    obtain ⟨hxp, hbad⟩ := lt_iSup_iff.mp hp
    obtain ⟨q, hqp, hq⟩ := exists_firstPrefixStop
      (fun q => t < dyadicBoxAverage I b q) hbad
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
      ⟨hq, dyadicDescendant_subset_of_isPrefix I hqp hxp⟩⟩
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hstop, hxp⟩ := Set.mem_iUnion.mp hp
    exact hstop.1.trans_le (dyadicBoxAverage_le_dyadicBoxMaximal I b p hxp)

/-- All strict superlevels are countable unions of measurable descendants,
so the literal dyadic maximal function is measurable for any input. -/
theorem measurable_dyadicBoxMaximal {d : ℕ}
    (I : Box (Fin d)) (b : Vec d → ℝ) : Measurable (dyadicBoxMaximal I b) := by
  classical
  apply measurable_of_Ioi
  intro t
  change MeasurableSet {x | t < dyadicBoxMaximal I b x}
  rw [set_lt_dyadicBoxMaximal_eq_firstStops]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
    measurableSet_dyadicDescendant I p

end PDE
