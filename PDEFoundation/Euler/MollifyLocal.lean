module

public import PDEFoundation.Euler.MollifyPeriodic

/-!
# Local integrability of periodic `L¹(cube)` functions
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem IsTorusPeriodic.sub_latVec {β : Type*} {f : Vec 2 → β} (hf : IsTorusPeriodic f) (k : Fin 2 → ℤ)
    (x : Vec 2) : f (x - latVec k) = f x := by
  have := hf.add_lattice (fun i => - k i) x
  have h2 : (∑ i, (((-k i : ℤ) : ℝ)) • basisVec i) = - latVec k := by
    simp only [latVec, Int.cast_neg, neg_smul, Finset.sum_neg_distrib]
  rw [h2, ← sub_eq_add_neg] at this
  exact this

theorem integrableOn_translate_cube {f : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hint : IntegrableOn f torusCube) (k : Fin 2 → ℤ) :
    IntegrableOn f ((fun x => x - latVec k) ⁻¹' torusCube) := by
  have hmp := measurePreserving_sub_right (volume : Measure (Vec 2)) (latVec k)
  have := (hmp.integrableOn_comp_preimage (measurableEmbedding_subRight (latVec k))
    (f := f) (s := torusCube)).2 hint
  have hfun : f ∘ (fun x => x - latVec k) = f := funext fun x => hf.sub_latVec k x
  rwa [hfun] at this

theorem IsTorusPeriodic.locallyIntegrable {f : Vec 2 → ℝ} (hf : IsTorusPeriodic f)
    (hint : IntegrableOn f torusCube) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec 2)
  obtain ⟨N, hN⟩ := exists_nat_ge R
  set F : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N with hF
  have hcover : K ⊆ ⋃ k ∈ (F : Set (Fin 2 → ℤ)), (fun x => x - latVec k) ⁻¹' torusCube := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa using hR hx
    simp only [mem_iUnion, mem_preimage, Finset.mem_coe]
    refine ⟨fun i => ⌊x i⌋, ?_, ?_⟩
    · rw [hF, Fintype.mem_piFinset]
      intro i
      have hxi : |x i| ≤ N := le_trans (norm_le_pi_norm x i) (hxR.trans hN)
      have h1 := abs_le.mp hxi
      rw [Finset.mem_Icc]
      constructor
      · have : (-(N : ℝ)) ≤ x i := h1.1
        have h2 : ((-(N : ℤ) : ℤ) : ℝ) ≤ x i := by push_cast; exact this
        exact Int.le_floor.mpr h2
      · exact (Int.floor_mono h1.2).trans (Int.floor_natCast N).le
    · constructor <;> intro i <;> simp only [Pi.sub_apply, latVec_apply, Pi.zero_apply, Pi.one_apply]
      · linarith [Int.floor_le (x i)]
      · linarith [Int.lt_floor_add_one (x i)]
  refine IntegrableOn.mono_set ?_ hcover
  exact (integrableOn_finite_biUnion F.finite_toSet).2 fun k _ => integrableOn_translate_cube hf hint k

/-- A periodic function satisfying a property a.e. on the cube satisfies it a.e. on `Vec 2`. -/
theorem IsTorusPeriodic.ae_of_ae_cube {β : Type*} {f : Vec 2 → β} (hf : IsTorusPeriodic f) {P : β → Prop}
    (h : ∀ᵐ x ∂(volume.restrict torusCube), P (f x)) : ∀ᵐ x ∂(volume : Measure (Vec 2)), P (f x) := by
  have hcube : MeasurableSet torusCube := measurableSet_Icc
  set N : Set (Vec 2) := {x | ¬ P (f x)} with hN
  have hNc : volume (N ∩ torusCube) = 0 := by
    have := h
    rw [ae_iff, Measure.restrict_apply' hcube] at this
    exact this
  rw [ae_iff]
  show volume N = 0
  have hsub : N ⊆ ⋃ k : Fin 2 → ℤ, (fun x => x - latVec k) ⁻¹' (N ∩ torusCube) := by
    intro x hx
    simp only [mem_iUnion, mem_preimage]
    refine ⟨fun i => ⌊x i⌋, ?_, ?_⟩
    · show ¬ P (f (x - latVec _))
      rw [hf.sub_latVec]; exact hx
    · constructor <;> intro i <;> simp only [Pi.sub_apply, latVec_apply, Pi.zero_apply, Pi.one_apply]
      · linarith [Int.floor_le (x i)]
      · linarith [Int.lt_floor_add_one (x i)]
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  rw [(measurePreserving_sub_right (volume : Measure (Vec 2)) (latVec k)).measure_preimage_emb
    (measurableEmbedding_subRight (latVec k))]
  exact hNc

end PDE
