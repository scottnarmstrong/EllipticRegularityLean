module

public import PDEFoundation.Measure.DyadicStoppingGeneration

/-! # Literal remainders of dyadic oscillation stops -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d m : ℕ}

/-- The union of all literal first oscillation-stopping descendants. -/
def dyadicOscillationStopUnion (I : Box (Fin d)) (g : Vec d → Vec m) :
    Set (Vec d) :=
  ⋃ q : List (Set (Fin d)),
    ⋃ (_ : IsFirstPrefixStop (dyadicOscillationBad I g) q),
      (dyadicDescendant I q : Set (Vec d))

/-- The part of a descendant left after removing all of its local first
oscillation stops. -/
def dyadicSparseRemainder (I : Box (Fin d)) (g : Vec d → Vec m)
    (p : List (Set (Fin d))) : Set (Vec d) :=
  (dyadicDescendant I p : Set (Vec d)) \
    dyadicOscillationStopUnion (dyadicDescendant I p) g

/-- All paths occurring in some literal recursive stopping generation. -/
def dyadicSparseFamily (I : Box (Fin d)) (g : Vec d → Vec m) :
    Set (List (Set (Fin d))) :=
  {p | ∃ n, p ∈ dyadicStoppingGeneration I g n}

theorem nil_mem_dyadicSparseFamily (I : Box (Fin d)) (g : Vec d → Vec m) :
    [] ∈ dyadicSparseFamily I g :=
  ⟨0, (mem_dyadicStoppingGeneration_zero I g []).2 rfl⟩

theorem measurableSet_dyadicOscillationStopUnion
    (I : Box (Fin d)) (g : Vec d → Vec m) :
    MeasurableSet (dyadicOscillationStopUnion I g) := by
  unfold dyadicOscillationStopUnion
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_dyadicDescendant I q

theorem dyadicOscillationStopUnion_subset
    (I : Box (Fin d)) (g : Vec d → Vec m) :
    dyadicOscillationStopUnion I g ⊆ (I : Set (Vec d)) := by
  intro x hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_hq, hxq⟩ := Set.mem_iUnion.mp hx
  exact dyadicDescendant_le I q hxq

theorem measurableSet_dyadicSparseRemainder
    (I : Box (Fin d)) (g : Vec d → Vec m)
    (p : List (Set (Fin d))) :
    MeasurableSet (dyadicSparseRemainder I g p) :=
  (measurableSet_dyadicDescendant I p).diff
    (measurableSet_dyadicOscillationStopUnion (dyadicDescendant I p) g)

theorem dyadicSparseRemainder_subset
    (I : Box (Fin d)) (g : Vec d → Vec m)
    (p : List (Set (Fin d))) :
    dyadicSparseRemainder I g p ⊆
      (dyadicDescendant I p : Set (Vec d)) :=
  Set.sdiff_subset

/-- Each literal local remainder occupies at least three quarters of its
parent descendant. -/
theorem three_quarters_mul_volume_dyadicDescendant_le_remainder
    (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m,
      MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (p : List (Set (Fin d))) :
    (3 / 4 : ℝ≥0∞) * volume (dyadicDescendant I p : Set (Vec d)) ≤
      volume (dyadicSparseRemainder I g p) := by
  let J := dyadicDescendant I p
  let U := dyadicOscillationStopUnion J g
  have hgJ : ∀ i : Fin m,
      MemLp (fun x => g x i) 2 (volumeOn (J : Set (Vec d))) := fun i =>
    (hg i).mono_measure (Measure.restrict_mono (dyadicDescendant_le I p) le_rfl)
  have hpack : volume U ≤ (4 : ℝ≥0∞)⁻¹ * volume (J : Set (Vec d)) := by
    simpa only [U, dyadicOscillationStopUnion, dyadicOscillationBad] using!
      volume_iUnion_firstPrefixStop_vecNormSq_le J g hgJ
  have hUsub : U ⊆ (J : Set (Vec d)) :=
    dyadicOscillationStopUnion_subset J g
  have hUmeas : MeasurableSet U := measurableSet_dyadicOscillationStopUnion J g
  have hUtop : volume U ≠ ∞ :=
    ((measure_mono hUsub).trans_lt (J.measure_coe_lt_top volume)).ne
  have hdiff : volume ((J : Set (Vec d)) \ U) =
      volume (J : Set (Vec d)) - volume U :=
    measure_sdiff hUsub hUmeas.nullMeasurableSet hUtop
  change (3 / 4 : ℝ≥0∞) * volume (J : Set (Vec d)) ≤
    volume ((J : Set (Vec d)) \ U)
  rw [hdiff]
  have hid : (3 / 4 : ℝ≥0∞) * volume (J : Set (Vec d)) =
      volume (J : Set (Vec d)) - (4 : ℝ≥0∞)⁻¹ *
        volume (J : Set (Vec d)) := by
    have hJtop : volume (J : Set (Vec d)) ≠ ∞ :=
      (J.measure_coe_lt_top volume).ne
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top (by finiteness) hJtop)
      (ENNReal.sub_ne_top hJtop)).mp
    have hquarter : (4 : ℝ≥0∞)⁻¹ * volume (J : Set (Vec d)) ≤
        volume (J : Set (Vec d)) :=
      mul_le_of_le_one_left (zero_le) (by norm_num)
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hquarter hJtop]
    norm_num [ENNReal.toReal_div]
    ring
  rw [hid]
  exact tsub_le_tsub_left hpack _

end

end PDE
