module

public import PDEFoundation.Measure.DyadicSparseDisjoint
public import PDEFoundation.Measure.DyadicSparseDomination
public import PDEFoundation.Measure.DyadicSparseEssentialInfNorm
public import PDEFoundation.Measure.DyadicSparseRemainder

/-!
# The oscillation decomposition (Lemma 3.6)

The manuscript's single statement, packaged from the dyadic sparse family `dyadicSparseFamily I g`:
a `3/4`-sparse family of dyadic subcubes containing the root, the pointwise domination of
`|g - (g)_{Q_0}|` by `2^{1+d/2} Σ_{Q ∈ S} e_Q 1_Q`, and the `L^p` bound `(4/3) p` for the sparse
sum of essential infima.
-/

@[expose] public section

open MeasureTheory BoxIntegral
open scoped ENNReal

namespace PDE

/-- **Oscillation decomposition** (Lemma 3.6, single root cube). -/
theorem exists_sparse_oscillation_decomposition {d m : ℕ} (I : Box (Fin d)) (hd : 0 < d) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    ∃ S : Set (List (Set (Fin d))), [] ∈ S ∧
      (∃ E : List (Set (Fin d)) → Set (Vec d),
        (∀ q ∈ S, MeasurableSet (E q) ∧ E q ⊆ (dyadicDescendant I q : Set (Vec d)) ∧
          (3/4 : ℝ≥0∞) * volume (dyadicDescendant I q : Set (Vec d)) ≤ volume (E q)) ∧
        S.Pairwise fun p q => Disjoint (E p) (E q)) ∧
      (∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
        ENNReal.ofReal (vecEuclideanNorm (g x - coordinateVectorAverage (I : Set (Vec d)) g)) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
            dyadicSparseSum I S (dyadicMeanOscillation I g) x) ∧
      ∀ (b : Vec d → ℝ) {p : ℝ}, 1 < p →
        MemLp b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) →
        eLpNorm (dyadicSparseSum I S (dyadicBoxEssentialInfReal I b)) (ENNReal.ofReal p)
            (volume.restrict (I : Set (Vec d))) ≤
          ENNReal.ofReal ((4/3 : ℝ) * p) * eLpNorm b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) := by
  refine ⟨dyadicSparseFamily I g, nil_mem_dyadicSparseFamily I g,
    ⟨dyadicSparseRemainder I g, fun q _ => ⟨measurableSet_dyadicSparseRemainder I g q,
      dyadicSparseRemainder_subset I g q, ?_⟩, pairwiseDisjoint_dyadicSparseRemainder I g⟩,
    ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_dyadicSparseSum I hd g hg,
    fun b p hp hb => eLpNorm_dyadicSparseSum_essentialInf_le I g hg b hp hb⟩
  have h34 : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]; norm_num
  simpa only [h34] using three_quarters_mul_volume_dyadicDescendant_le_remainder I g hg q

end PDE
