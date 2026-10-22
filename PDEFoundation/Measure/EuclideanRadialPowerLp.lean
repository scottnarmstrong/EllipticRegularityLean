module

public import PDEFoundation.Measure.EuclideanRadialPower
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Native `Lᵖ` membership of Euclidean radial powers -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- On a native round ball, the scalar radial power `|x|^s` belongs to finite
real `Lᵖ` exactly when `s p > -d`. -/
theorem memLp_vecEuclideanNorm_rpow_euclideanBall_iff
    {d : ℕ} (hd : 0 < d) {R s p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    MemLp (fun x : Vec d => vecEuclideanNorm x ^ s) (ENNReal.ofReal p)
        (volume.restrict (euclideanBall 0 R)) ↔
      -(d : ℝ) < s * p := by
  let f : Vec d → ℝ := fun x => vecEuclideanNorm x ^ s
  have hfcont : ContinuousOn f ({0}ᶜ : Set (Vec d)) := by
    apply continuous_vecEuclideanNorm.continuousOn.rpow_const
    intro x hx
    left
    exact (vecEuclideanNorm_pos_iff.2 (by simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hx)).ne'
  have hfmeas : Measurable f :=
    measurable_of_continuousOn_compl_singleton 0 hfcont
  have hfAES : AEStronglyMeasurable f
      (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    hfmeas.aestronglyMeasurable
  have hpZero : ENNReal.ofReal p ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hp) (ENNReal.ofReal_eq_zero.mp hzero)
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [← integrable_norm_rpow_iff hfAES hpZero hpTop]
  have hfun : (fun x : Vec d => ‖f x‖ ^ (ENNReal.ofReal p).toReal) =
      fun x => vecEuclideanNorm x ^ (s * p) := by
    funext x
    dsimp only [f]
    rw [ENNReal.toReal_ofReal hp.le, Real.norm_rpow_of_nonneg (vecEuclideanNorm_nonneg x),
      Real.norm_of_nonneg (vecEuclideanNorm_nonneg x)]
    exact (Real.rpow_mul (vecEuclideanNorm_nonneg x) s p).symm
  rw [hfun]
  change IntegrableOn (fun x : Vec d => vecEuclideanNorm x ^ (s * p))
      (euclideanBall 0 R) ↔ _
  exact integrableOn_vecEuclideanNorm_rpow_euclideanBall_iff hd hR

end

end PDE
