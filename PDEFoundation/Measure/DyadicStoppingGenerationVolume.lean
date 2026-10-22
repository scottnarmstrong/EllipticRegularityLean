module

public import PDEFoundation.Measure.DyadicStoppingGeneration

/-! # Volume decay of recursive dyadic stopping generations -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal Function

/-- The literal union of descendant carriers in stopping generation `n`. -/
def dyadicStoppingRegion {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (n : ℕ) : Set (Vec d) :=
  ⋃ p : {p // p ∈ dyadicStoppingGeneration I g n},
    (dyadicDescendant I p.1 : Set (Vec d))

theorem measurableSet_dyadicStoppingRegion {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (n : ℕ) : MeasurableSet (dyadicStoppingRegion I g n) := by
  exact MeasurableSet.iUnion fun p => measurableSet_dyadicDescendant I p.1

@[simp]
theorem dyadicStoppingRegion_zero {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) : dyadicStoppingRegion I g 0 = (I : Set (Vec d)) := by
  ext x
  simp [dyadicStoppingRegion]

theorem dyadicStoppingRegion_succ_subset {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m) (n : ℕ) :
    dyadicStoppingRegion I g (n + 1) ⊆ dyadicStoppingRegion I g n := by
  intro x hx
  obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
  have hrmem := r.2
  rw [mem_dyadicStoppingGeneration_succ] at hrmem
  obtain ⟨p, hp, q, _hq, hr⟩ := hrmem
  apply Set.mem_iUnion.mpr
  refine ⟨⟨p, hp⟩, ?_⟩
  rw [hr, dyadicDescendant_append] at hxr
  exact dyadicDescendant_le (dyadicDescendant I p) q hxr

/-- Each recursive generation has at most one quarter of the preceding
generation's volume. -/
theorem volume_dyadicStoppingRegion_succ_le {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (n : ℕ) :
    volume (dyadicStoppingRegion I g (n + 1)) ≤
      (4 : ℝ≥0∞)⁻¹ * volume (dyadicStoppingRegion I g n) := by
  let P := {p // p ∈ dyadicStoppingGeneration I g n}
  let E : P → Set (Vec d) := fun p =>
    ⋃ q : List (Set (Fin d)),
      ⋃ (_ : IsFirstPrefixStop (dyadicOscillationBad (dyadicDescendant I p.1) g) q),
        (dyadicDescendant (dyadicDescendant I p.1) q : Set (Vec d))
  have hcover : dyadicStoppingRegion I g (n + 1) ⊆ ⋃ p : P, E p := by
    intro x hx
    obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
    have hrmem := r.2
    rw [mem_dyadicStoppingGeneration_succ] at hrmem
    obtain ⟨p, hp, q, hq, hr⟩ := hrmem
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, ?_⟩⟩
    rwa [hr, dyadicDescendant_append] at hxr
  have hlocal (p : P) : volume (E p) ≤
      (4 : ℝ≥0∞)⁻¹ * volume (dyadicDescendant I p.1 : Set (Vec d)) := by
    have hsub : (dyadicDescendant I p.1 : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
      dyadicDescendant_le I p.1
    have hg' : ∀ i : Fin m, MemLp (fun x => g x i) 2
        (volumeOn (dyadicDescendant I p.1 : Set (Vec d))) := by
      intro i
      exact (hg i).mono_measure (Measure.restrict_mono hsub le_rfl)
    exact volume_iUnion_firstPrefixStop_vecNormSq_le (dyadicDescendant I p.1) g hg'
  calc
    volume (dyadicStoppingRegion I g (n + 1)) ≤ volume (⋃ p : P, E p) :=
      measure_mono hcover
    _ ≤ ∑' p : P, volume (E p) := measure_iUnion_le _
    _ ≤ ∑' p : P, (4 : ℝ≥0∞)⁻¹ *
        volume (dyadicDescendant I p.1 : Set (Vec d)) :=
      ENNReal.tsum_le_tsum hlocal
    _ = (4 : ℝ≥0∞)⁻¹ * ∑' p : P,
        volume (dyadicDescendant I p.1 : Set (Vec d)) := ENNReal.tsum_mul_left
    _ = (4 : ℝ≥0∞)⁻¹ * volume (dyadicStoppingRegion I g n) := by
      congr 1
      rw [dyadicStoppingRegion, measure_iUnion]
      · exact pairwiseDisjoint_dyadicStoppingGeneration I g n |>.subtype
      · intro p
        exact measurableSet_dyadicDescendant I p.1

/-- Geometric volume decay of the literal recursive stopping regions. -/
theorem volume_dyadicStoppingRegion_le {d m : ℕ} (I : Box (Fin d))
    (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (n : ℕ) :
    volume (dyadicStoppingRegion I g n) ≤
      ((4 : ℝ≥0∞)⁻¹) ^ n * volume (I : Set (Vec d)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        volume (dyadicStoppingRegion I g (n + 1)) ≤
            (4 : ℝ≥0∞)⁻¹ * volume (dyadicStoppingRegion I g n) :=
          volume_dyadicStoppingRegion_succ_le I g hg n
        _ ≤ (4 : ℝ≥0∞)⁻¹ *
            (((4 : ℝ≥0∞)⁻¹) ^ n * volume (I : Set (Vec d))) :=
          mul_le_mul_right ih _
        _ = ((4 : ℝ≥0∞)⁻¹) ^ (n + 1) * volume (I : Set (Vec d)) := by
          rw [pow_succ]
          ac_rfl

end PDE
