module

public import EllipticRegularity.Parabolic.Rescale.AffineMaps

/-!
# Essential bounds under an affine change of variables

For an arbitrary (not necessarily measurable) `f`, the essential supremum and infimum of
`y ↦ f (c + r • y)` over a Euclidean ball are those of `f` over the image ball.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

theorem essSup_comp_affine_euclideanBall {d : ℕ} (f : Vec d → ℝ≥0∞) (c w : Vec d) {r : ℝ}
    (hr : 0 < r) (ρ : ℝ) :
    essSup (fun y => f (c + r • y)) (volume.restrict (euclideanBall w ρ)) =
      essSup f (volume.restrict (euclideanBall (c + r • w) (r * ρ))) := by
  have h := map_restrict_spaceMap c hr (euclideanBall w ρ)
  rw [spaceMap_image_euclideanBall c w hr ρ] at h
  exact essSup_comp_of_map_eq_smul (spaceMap_measurableEmbedding c hr)
    (ofReal_inv_pow_ne_zero hr d) h f

theorem essInf_comp_affine_euclideanBall {d : ℕ} (f : Vec d → ℝ≥0∞) (c w : Vec d) {r : ℝ}
    (hr : 0 < r) (ρ : ℝ) :
    essInf (fun y => f (c + r • y)) (volume.restrict (euclideanBall w ρ)) =
      essInf f (volume.restrict (euclideanBall (c + r • w) (r * ρ))) := by
  have h := map_restrict_spaceMap c hr (euclideanBall w ρ)
  rw [spaceMap_image_euclideanBall c w hr ρ] at h
  exact essInf_comp_of_map_eq_smul (spaceMap_measurableEmbedding c hr)
    (ofReal_inv_pow_ne_zero hr d) h f

end PDE.Parabolic.Rescale
