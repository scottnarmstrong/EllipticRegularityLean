module

public import PDEFoundation.Measure.BallMaximalAverage
public import PDEFoundation.Measure.CompactBallCoverEstimate
public import PDEFoundation.Measure.CompactVolumeBound

/-!
# Weak estimate for the uncentered ball maximal function

The proof combines literal maximal-function witnesses, compact finite
subcovers, and inner regularity of Lebesgue measure.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- The uncentered maximal function over native round balls satisfies the
weak `(1, 1)` estimate with the triple-dilate constant. -/
theorem volume_set_lt_uncenteredBallMaximal_le
    {d : ℕ} (b : Vec d → ℝ) (t : ℝ) (ht : 0 < t)
    (hb : Integrable b volume) :
    volume {x | ENNReal.ofReal t < uncenteredBallMaximal b x} ≤
      ENNReal.ofReal
        ((3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume) := by
  let U : Set (Vec d) :=
    {x | ENNReal.ofReal t < uncenteredBallMaximal b x}
  have hUopen : IsOpen U := by
    change IsOpen (uncenteredBallMaximal b ⁻¹' Ioi (ENNReal.ofReal t))
    exact (lowerSemicontinuous_uncenteredBallMaximal b).isOpen_preimage _
  have hCnonneg :
      0 ≤ (3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume :=
    mul_nonneg (div_nonneg (by positivity) ht.le)
      (integral_nonneg fun x => abs_nonneg (b x))
  apply volume_isOpen_le_of_compact_toReal_le hUopen hCnonneg
  intro K hKU hK
  apply volume_compact_toReal_le_of_euclideanBall_average_gt
    hK b t ht hb
  intro x hxK
  have hxU : ENNReal.ofReal t < uncenteredBallMaximal b x := hKU hxK
  have hxUnion : x ∈
      ⋃ z : Vec d, ⋃ R : ℝ, ⋃ (_hR : 0 < R),
        ⋃ (_havg : ENNReal.ofReal t <
          (volume (euclideanBall z R))⁻¹ *
            ∫⁻ y in euclideanBall z R, ENNReal.ofReal |b y|),
          euclideanBall z R := by
    rw [← set_lt_uncenteredBallMaximal b (ENNReal.ofReal t)]
    exact hxU
  simp only [Set.mem_iUnion] at hxUnion
  obtain ⟨z, R, hR, havg, hxBall⟩ := hxUnion
  have havg' :
      ENNReal.ofReal t <
        ENNReal.ofReal
          (integralAverage (euclideanBall z R) (fun y => |b y|)) := by
    rwa [ofReal_integralAverage_abs_eq_lintegralAverage b hR hb.integrableOn]
  have havgReal :
      t < integralAverage (euclideanBall z R) (fun y => |b y|) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp havg'
  have haverage :
      (⨍ y in euclideanBall z R, |b y| ∂volume) =
        integralAverage (euclideanBall z R) (fun y => |b y|) := by
    rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ,
      measureReal_def]
    rfl
  exact ⟨z, R, hR, hxBall, haverage.symm ▸ havgReal⟩

end PDE
