module

public import PDEFoundation.Measure.DyadicSparseForestNorm
public import PDEFoundation.Measure.DyadicSparseForestDomination

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

/-- The source forest norm on the union of roots, with countability derived
from the disjoint-interior hypothesis and no global source integrability added. -/
theorem eLpNorm_dyadicSparseForest_union_le
    {d m : ℕ} {ρ : Type*} (root : ρ → Box (Fin d))
    (hroot : Pairwise fun i j => Disjoint (Box.Ioo (root i)) (Box.Ioo (root j)))
    (g : ρ → Vec d → Vec m)
    (hg : ∀ i j, MemLp (fun x => g i x j) 2 (volumeOn (root i : Set (Vec d))))
    (b : Vec d → ℝ) {p : ℝ} (hp : 1 < p)
    (hb : MemLp b (ENNReal.ofReal p)
      (volume.restrict (⋃ i, (root i : Set (Vec d))))) :
    eLpNorm (fun x => ∑' i,
      dyadicSparseSum (root i) (dyadicSparseFamily (root i) (g i))
        (dyadicBoxEssentialInfReal (root i) b) x)
      (ENNReal.ofReal p) (volume.restrict (⋃ i, (root i : Set (Vec d)))) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        eLpNorm b (ENNReal.ofReal p)
          (volume.restrict (⋃ i, (root i : Set (Vec d)))) := by
  let : Countable ρ := countable_of_pairwiseDisjoint_box_Ioo root hroot
  let U : Set (Vec d) := ⋃ i, (root i : Set (Vec d))
  have hU : MeasurableSet U := MeasurableSet.iUnion fun i => (root i).measurableSet_coe
  let bExt : Vec d → ℝ := U.indicator b
  have hbExt : MemLp bExt (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict hU).mpr hb
  have hcoeff (i : ρ) : dyadicBoxEssentialInfReal (root i) bExt =
      dyadicBoxEssentialInfReal (root i) b := by
    funext q
    unfold dyadicBoxEssentialInfReal dyadicBoxEssentialInf
    congr 1
    apply essInf_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_dyadicDescendant (root i) q)] with x hx
    have hxroot := dyadicDescendant_le (root i) q hx
    have hxU : x ∈ U := Set.mem_iUnion.mpr ⟨i, hxroot⟩
    simp only [bExt, Set.indicator_of_mem hxU]
  have hnorm := eLpNorm_dyadicSparseForest_le root hroot g hg bExt hp hbExt
  simp only [hcoeff] at hnorm
  have hbNorm : eLpNorm bExt (ENNReal.ofReal p) volume =
      eLpNorm b (ENNReal.ofReal p) (volume.restrict U) :=
    eLpNorm_indicator_eq_eLpNorm_restrict hU
  rw [hbNorm] at hnorm
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hnorm

end PDE
