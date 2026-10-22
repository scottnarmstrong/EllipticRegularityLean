module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.CompletePartialOrder


/-!
# A function whose increments are integrals of a locally integrable function is continuous
-/

@[expose] public section

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology

theorem continuousOn_of_primitive {I : Set ℝ} (hI : I.OrdConnected) {E g : ℝ → ℝ}
    (h : ∀ s t, s ∈ I → t ∈ I → s < t →
      IntegrableOn g (Ioc s t) ∧ E t - E s = ∫ σ in Ioc s t, g σ) :
    ContinuousOn E I := by
  have hint : ∀ p ∈ I, ∀ q ∈ I, IntervalIntegrable g volume p q := by
    intro p hp q hq
    rcases lt_trichotomy p q with hpq | rfl | hqp
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq.le).2 (h p q hp hq hpq).1
    · exact IntervalIntegrable.refl
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hqp.le).2 (h q p hq hp hqp).1).symm
  have hrep : ∀ p ∈ I, ∀ t ∈ I, E t = E p + ∫ σ in p..t, g σ := by
    intro p hp t ht
    rcases lt_trichotomy p t with hpt | rfl | htp
    · rw [intervalIntegral.integral_of_le hpt.le, ← (h p t hp ht hpt).2]; ring
    · simp
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le htp.le,
        ← (h t p ht hp htp).2]; ring
  intro t0 ht0
  have hR : ContinuousWithinAt E (I ∩ Ici t0) t0 := by
    by_cases hb : ∃ b ∈ I, t0 < b
    · obtain ⟨b, hbI, hb⟩ := hb
      have hP : ContinuousOn (fun x => ∫ σ in t0..x, g σ) (uIcc t0 b) :=
        intervalIntegral.continuousOn_primitive_interval' (hint t0 ht0 b hbI) left_mem_uIcc
      have hEc : ContinuousOn E (Icc t0 b) := by
        have hsub : Icc t0 b ⊆ I := hI.out ht0 hbI
        have : ContinuousOn (fun x => E t0 + ∫ σ in t0..x, g σ) (Icc t0 b) :=
          continuousOn_const.add (hP.mono (by rw [uIcc_of_le hb.le]))
        exact this.congr fun x hx => hrep t0 ht0 x (hsub hx)
      refine (hEc.continuousWithinAt ⟨le_rfl, hb.le⟩).mono_of_mem_nhdsWithin ?_
      exact mem_of_superset (nhdsWithin_mono _ inter_subset_right (Icc_mem_nhdsGE hb)) (subset_refl _)
    · push Not at hb
      have : I ∩ Ici t0 ⊆ {t0} := fun x hx => le_antisymm (hb x hx.1) hx.2
      exact (continuousWithinAt_singleton).mono this
  have hL : ContinuousWithinAt E (I ∩ Iic t0) t0 := by
    by_cases hb : ∃ b ∈ I, b < t0
    · obtain ⟨b, hbI, hb⟩ := hb
      have hP : ContinuousOn (fun x => ∫ σ in t0..x, g σ) (uIcc b t0) :=
        intervalIntegral.continuousOn_primitive_interval' (hint t0 ht0 b hbI).symm right_mem_uIcc
      have hEc : ContinuousOn E (Icc b t0) := by
        have hsub : Icc b t0 ⊆ I := hI.out hbI ht0
        have : ContinuousOn (fun x => E t0 + ∫ σ in t0..x, g σ) (Icc b t0) :=
          continuousOn_const.add (hP.mono (by rw [uIcc_of_le hb.le]))
        exact this.congr fun x hx => hrep t0 ht0 x (hsub hx)
      refine (hEc.continuousWithinAt ⟨hb.le, le_rfl⟩).mono_of_mem_nhdsWithin ?_
      exact mem_of_superset (nhdsWithin_mono _ inter_subset_right (Icc_mem_nhdsLE hb)) (subset_refl _)
    · push Not at hb
      have : I ∩ Iic t0 ⊆ {t0} := fun x hx => le_antisymm hx.2 (hb x hx.1)
      exact (continuousWithinAt_singleton).mono this
  have hU := hL.union hR
  refine hU.mono ?_
  intro x hx
  rcases le_total x t0 with h1 | h1
  · exact Or.inl ⟨hx, h1⟩
  · exact Or.inr ⟨hx, h1⟩

end PDE.Parabolic.Energy
