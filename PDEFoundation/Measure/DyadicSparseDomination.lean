module

public import PDEFoundation.Measure.DyadicSparseGoodRecovery
public import PDEFoundation.Measure.DyadicStoppingTelescoping
public import PDEFoundation.Measure.DyadicSparseSum

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

/-- The actual recursive sparse family dominates the original oscillation,
with the exact dimension coefficient. All recovery and finite-chain inputs
are proved from the original coordinatewise L2 data inside this theorem. -/
theorem ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_dyadicSparseSum
    {d m : ℕ} (I : Box (Fin d)) (hd : 0 < d) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
      ENNReal.ofReal (vecEuclideanNorm
          (g x - coordinateVectorAverage (I : Set (Vec d)) g)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
          dyadicSparseSum I (dyadicSparseFamily I g) (dyadicMeanOscillation I g) x := by
  classical
  have hgood := ae_good_recovery_all_dyadicDescendants I hd g hg
  have hfinite := ae_restrict_of_ae (s := (I : Set (Vec d))) (ae_exists_not_mem_dyadicStoppingRegion I g hg)
  filter_upwards [hgood, hfinite, ae_restrict_mem I.measurableSet_coe] with x hxGood hxFinite hxI
  obtain ⟨N, hxN⟩ := hxFinite
  have hroot : [] ∈ dyadicStoppingGeneration I g 0 := by simp
  have hrootMem : x ∈ (dyadicDescendant I [] : Set (Vec d)) := hxI
  have hxN' : x ∉ dyadicStoppingRegion I g (0 + N) := by simpa using hxN
  obtain ⟨T, hT, hbound⟩ := finite_stopping_domination_of_good_recovery
    I g hg x hxGood N 0 [] hroot hrootMem hxN'
  have he : ∀ q ∈ dyadicSparseFamily I g, 0 ≤ dyadicMeanOscillation I g q :=
    fun q _ => Real.sqrt_nonneg _
  have hfilter : finsetWithinSet T (dyadicSparseFamily I g) = T := by
    ext q
    simp only [mem_finsetWithinSet]
    exact ⟨fun h => h.1, fun h => ⟨h, (hT q h).1⟩⟩
  have hsum : finiteSparseSum I T (dyadicMeanOscillation I g) x =
      ∑ q ∈ T, dyadicMeanOscillation I g q := by
    unfold finiteSparseSum
    apply Finset.sum_congr rfl
    intro q hq
    exact Set.indicator_of_mem (hT q hq).2.1 _
  have hpartial : ENNReal.ofReal (∑ q ∈ T, dyadicMeanOscillation I g q) ≤
      dyadicSparseSum I (dyadicSparseFamily I g) (dyadicMeanOscillation I g) x := by
    rw [dyadicSparseSum_eq_iSup_finiteSparseSum I _ _ he x]
    have h := le_iSup (fun U : Finset (List (Set (Fin d))) =>
      ENNReal.ofReal (finiteSparseSum I (finsetWithinSet U (dyadicSparseFamily I g))
        (dyadicMeanOscillation I g) x)) T
    simpa only [hfilter, hsum] using h
  have hreal := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)] at hreal
  exact hreal.trans (mul_le_mul_right hpartial _)

end PDE
