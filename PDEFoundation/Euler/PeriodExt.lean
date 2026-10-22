module

public import PDEFoundation.Euler.MollifyLocal

/-!
# Periodic extension of a function on the cube

`periodExt f x = f (x - ⌊x⌋)` is `ℤ²`-periodic and agrees with `f` a.e. on the cube.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- The `ℤ²`-periodic extension of the restriction of `f` to `[0,1)²`. -/
noncomputable def periodExt {β : Type*} (f : Vec 2 → β) : Vec 2 → β :=
  fun x => f (x - latVec (fun i => ⌊x i⌋))

theorem isTorusPeriodic_periodExt {β : Type*} (f : Vec 2 → β) : IsTorusPeriodic (periodExt f) := by
  intro i x
  simp only [periodExt]
  congr 1
  funext j
  simp only [Pi.sub_apply, Pi.add_apply, latVec_apply]
  by_cases hij : j = i
  · subst hij
    simp [Int.floor_add_one]
  · simp [basisVec, hij]

theorem periodExt_eq_of_lt_one {β : Type*} (f : Vec 2 → β) {x : Vec 2} (hx : x ∈ torusCube)
    (hx1 : ∀ i, x i < 1) : periodExt f x = f x := by
  simp only [periodExt]
  have : latVec (fun i => ⌊x i⌋) = 0 := by
    funext i
    rw [latVec_apply]
    have h0 : 0 ≤ x i := hx.1 i
    simp [Int.floor_eq_zero_iff, h0, hx1 i]
  rw [this, sub_zero]

theorem ae_cube_lt_one : ∀ᵐ x ∂(volume.restrict torusCube), ∀ i, x i < 1 := by
  have hm : MeasurableSet torusCube := measurableSet_Icc
  rw [ae_iff, Measure.restrict_apply' hm]
  have hsub : {x : Vec 2 | ¬ ∀ i, x i < 1} ∩ torusCube ⊆
      ⋃ i : Fin 2, Icc (Function.update (0 : Vec 2) i 1) 1 := by
    intro x ⟨hx, hc⟩
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    simp only [mem_iUnion]
    refine ⟨i, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; exact hi
      · simp only [Function.update_of_ne hj, Pi.zero_apply]; exact hc.1 j
    · exact hc.2
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  rw [Real.volume_Icc_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

theorem ae_periodExt_eq {β : Type*} (f : Vec 2 → β) :
    ∀ᵐ x ∂(volume.restrict torusCube), periodExt f x = f x := by
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_cube_lt_one] with x hx hx1
  exact periodExt_eq_of_lt_one f hx hx1

end PDE
