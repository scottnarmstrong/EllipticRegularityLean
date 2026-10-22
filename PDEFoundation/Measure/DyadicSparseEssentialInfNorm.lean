module

public import PDEFoundation.Measure.DyadicSparseSum
public import PDEFoundation.Measure.DyadicSparseDisjoint
public import PDEFoundation.Measure.DyadicBoxEssentialInf

/-! # Strong norm of the source dyadic essential-infimum sparse sum -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped _root_.ENNReal

noncomputable section

variable {d m : ℕ}

/-- The literal recursively generated sparse family, equipped with its actual
remainder sets and essential-infimum coefficients, satisfies the sharp
countable sparse `Lᵖ` bound. -/
theorem eLpNorm_dyadicSparseSum_essentialInf_le
    (I : Box (Fin d)) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m,
      MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d))))
    (b : Vec d → ℝ) {p : ℝ} (hp : 1 < p)
    (hb : MemLp b (ENNReal.ofReal p)
      (volume.restrict (I : Set (Vec d)))) :
    eLpNorm
        (dyadicSparseSum I (dyadicSparseFamily I g)
          (dyadicBoxEssentialInfReal I b))
        (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        eLpNorm b (ENNReal.ofReal p)
          (volume.restrict (I : Set (Vec d))) := by
  apply eLpNorm_dyadicSparseSum_le I (dyadicSparseFamily I g) b
    (dyadicBoxEssentialInfReal I b) (dyadicSparseRemainder I g)
  · intro q hq
    exact dyadicBoxEssentialInfReal_nonneg I b q
  · intro q hq
    exact measurableSet_dyadicSparseRemainder I g q
  · intro q hq
    exact dyadicSparseRemainder_subset I g q
  · exact pairwiseDisjoint_dyadicSparseRemainder I g
  · intro q hq
    have h34 : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
    simpa only [h34] using
      three_quarters_mul_volume_dyadicDescendant_le_remainder I g hg q
  · intro q hq
    exact ae_dyadicBoxEssentialInfReal_le I b q
  · exact hp
  · exact hb

/-- For an almost everywhere nonnegative source, the real coefficient in the
source sparse sum re-embeds as the literal essential infimum of the source
itself on every descendant. -/
theorem ofReal_dyadicBoxEssentialInfReal_eq_essInf_of_ae_nonneg
    (I : Box (Fin d)) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (I : Set (Vec d)), 0 ≤ b x)
    (q : List (Set (Fin d))) :
    ENNReal.ofReal (dyadicBoxEssentialInfReal I b q) =
      essInf (fun x => ENNReal.ofReal (b x))
        (volume.restrict (dyadicDescendant I q : Set (Vec d))) := by
  rw [ofReal_dyadicBoxEssentialInfReal]
  apply dyadicBoxEssentialInf_eq_essInf_of_ae_nonneg
  exact ae_restrict_of_ae_restrict_of_subset (dyadicDescendant_le I q) hb

end

end PDE
