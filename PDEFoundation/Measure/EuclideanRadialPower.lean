module

public import PDEFoundation.Analysis.HilbertRadialIntegrability
public import PDEFoundation.Analysis.HilbertDictionary

/-! # Integrability of native Euclidean radial powers -/

@[expose] public section

open MeasureTheory Metric

namespace PDE

noncomputable section

/-- On a native round ball, `|x|^s` is integrable at the origin exactly when
`s > -d`. -/
theorem integrableOn_vecEuclideanNorm_rpow_euclideanBall_iff
    {d : ℕ} (hd : 0 < d) {R s : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : Vec d => vecEuclideanNorm x ^ s)
        (euclideanBall 0 R) ↔
      -(d : ℝ) < s := by
  let : NeZero d := ⟨hd.ne'⟩
  have htransport := Internal.measurePreserving_toHilbert.integrableOn_comp_preimage
    (Internal.toHilbert : Vec d ≃L[ℝ] HilbertVec d).toHomeomorph.measurableEmbedding
    (f := fun z : HilbertVec d => ‖z‖ ^ s) (s := Metric.ball 0 R)
  have hpre : Internal.toHilbert ⁻¹' Metric.ball (0 : HilbertVec d) R =
      euclideanBall (0 : Vec d) R := by
    simpa only [map_zero] using Internal.preimage_ball_toHilbert (0 : Vec d) hR
  rw [hpre] at htransport
  have hnative : (fun z : HilbertVec d => ‖z‖ ^ s) ∘ Internal.toHilbert =
      fun x : Vec d => vecEuclideanNorm x ^ s := by
    funext x
    simp only [Function.comp_apply, Internal.toHilbert_apply,
      ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  rw [hnative] at htransport
  rw [htransport]
  exact Internal.integrableOn_norm_rpow_euclideanBall_iff hR

end

end PDE
