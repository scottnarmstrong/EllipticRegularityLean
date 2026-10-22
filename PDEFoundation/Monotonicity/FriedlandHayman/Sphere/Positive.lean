module

public import PDEFoundation.Monotonicity.Core.BridgeSphere

/-!
# Friedland--Hayman: positivity of the sphere measure of open sets

Nonempty relatively open subsets of the unit sphere have positive surface measure.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- Nonempty relatively open subsets of the unit sphere have positive measure. -/
theorem sphereIntegral_indicator_pos {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hne : (U ∩ euclideanSphere (0 : Vec d) 1).Nonempty) :
    0 < sphereIntegral (0 : Vec d) 1 (U.indicator fun _ => (1 : ℝ)) := by
  obtain ⟨x, hxU, hxS⟩ := hne
  have hn : ‖x.toHilbertVec‖ = 1 := by
    rw [← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
    have hsq : vecEuclideanNorm x ^ 2 = 1 := by
      rw [vecEuclideanNorm_sq]
      have h : euclideanSqDist x 0 = 1 ^ 2 := hxS
      simpa [euclideanSqDist] using h
    nlinarith [vecEuclideanNorm_nonneg x]
  set V : Set (Metric.sphere (0 : HilbertVec d) 1) :=
    {ω | (ω : HilbertVec d).toVec ∈ U} with hV
  have hVo : IsOpen V :=
    hU.preimage (continuous_toVec.comp continuous_subtype_val)
  have hVne : V.Nonempty := ⟨⟨x.toHilbertVec, by simpa using hn⟩, hxU⟩
  have hpos : 0 < ((volume : Measure (HilbertVec d)).toSphere).real V :=
    ENNReal.toReal_pos (hVo.measure_pos _ hVne).ne' (measure_ne_top _ _)
  have hint : sphereIntegral (0 : Vec d) 1 (U.indicator fun _ => (1 : ℝ)) =
      ((volume : Measure (HilbertVec d)).toSphere).real V := by
    unfold sphereIntegral
    simp only [one_pow, one_mul, zero_add, one_smul]
    rw [← integral_indicator_one hVo.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases h : (ω : HilbertVec d).toVec ∈ U
    · simp [Set.indicator, hV, h]
    · simp [Set.indicator, hV, h]
  rw [hint]
  exact hpos

end

end PDE.FHLane
