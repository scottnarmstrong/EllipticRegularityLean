module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Weights

/-!
# Friedland--Hayman: symmetry and surjectivity of the Gaussian tail

`gaussTail (-t) = 1 - gaussTail t`, and `gaussTail` takes every value in `(0, 1)`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

theorem gaussTail_neg (t : ℝ) : gaussTail (-t) = 1 - gaussTail t := by
  have hI : Integrable gaussW := integrable_gaussW
  have h1 : ∫ s in Ioi (-t), gaussW s = ∫ s in Iic t, gaussW s := by
    have := integral_comp_neg_Ioi (-t) gaussW
    rw [neg_neg] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [gaussW]
  have h2 : (∫ s in Iic t, gaussW s) + ∫ s in Ioi t, gaussW s = ∫ s, gaussW s := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hI.integrableOn hI.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  have hpos : (∫ s, gaussW s) ≠ 0 := Transp.gTot_pos.ne'
  unfold gaussTail
  rw [h1]
  field_simp
  linarith

theorem exists_gaussTail_eq {m : ℝ} (hm : m ∈ Set.Ioo 0 1) : ∃ t, gaussTail t = m := by
  obtain ⟨a, ha⟩ := (tendsto_gaussTail_atBot.eventually (lt_mem_nhds hm.2)).exists
  obtain ⟨b, hb⟩ := (tendsto_gaussTail_atTop.eventually (gt_mem_nhds hm.1)).exists
  exact mem_range_of_exists_le_of_exists_ge continuous_gaussTail ⟨b, hb.le⟩ ⟨a, ha.le⟩

end

end PDE.FHLane
