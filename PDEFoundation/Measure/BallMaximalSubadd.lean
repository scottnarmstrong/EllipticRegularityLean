module

public import PDEFoundation.Measure.BallMaximal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Subadditivity and bounded inputs for the literal ball maximal function -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

theorem uncenteredBallMaximal_add_le
    {d : ℕ} (f g : Vec d → ℝ) (hf : AEStronglyMeasurable f volume) (x : Vec d) :
    uncenteredBallMaximal (fun y => f y + g y) x ≤
      uncenteredBallMaximal f x + uncenteredBallMaximal g x := by
  unfold uncenteredBallMaximal
  refine iSup_le fun z => iSup_le fun R => iSup_le fun hR => iSup_le fun hx => ?_
  have hpoint (y : Vec d) : ENNReal.ofReal |f y + g y| ≤
      ENNReal.ofReal |f y| + ENNReal.ofReal |g y| :=
    (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans ENNReal.ofReal_add_le
  have hf' : AEMeasurable (fun y => ENNReal.ofReal |f y|) volume := by
    simpa only [Real.enorm_eq_ofReal_abs] using hf.enorm
  have hsum := (lintegral_mono (μ := volume.restrict (euclideanBall z R)) hpoint).trans_eq
    (lintegral_add_left' hf'.restrict _)
  have haverage := mul_le_mul_right hsum (volume (euclideanBall z R))⁻¹
  rw [mul_add] at haverage
  exact haverage.trans (add_le_add
    (lintegralAverage_le_uncenteredBallMaximal f hR hx)
    (lintegralAverage_le_uncenteredBallMaximal g hR hx))

/-- An almost everywhere bound on the input bounds every literal ball
average, hence the full uncentered maximal function. -/
theorem uncenteredBallMaximal_le_of_ae_abs_le
    {d : ℕ} (b : Vec d → ℝ) {s : ℝ}
    (hb : ∀ᵐ y ∂volume, |b y| ≤ s) (x : Vec d) :
    uncenteredBallMaximal b x ≤ ENNReal.ofReal s := by
  unfold uncenteredBallMaximal
  refine iSup_le fun z => iSup_le fun R => iSup_le fun hR => iSup_le fun _ => ?_
  have hpoint : (fun y => ENNReal.ofReal |b y|) ≤ᵐ[volume.restrict (euclideanBall z R)]
      fun _ => ENNReal.ofReal s :=
    (ae_restrict_of_ae hb).mono fun _ hy => ENNReal.ofReal_le_ofReal hy
  calc
    (volume (euclideanBall z R))⁻¹ *
        (∫⁻ y in euclideanBall z R, ENNReal.ofReal |b y|) ≤
      (volume (euclideanBall z R))⁻¹ * (∫⁻ _y in euclideanBall z R, ENNReal.ofReal s) :=
        mul_le_mul_right (lintegral_mono_ae hpoint) _
    _ = ENNReal.ofReal s := by
      rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (ENNReal.ofReal s),
        ENNReal.inv_mul_cancel_left (volume_euclideanBall_pos z hR).ne'
          (volume_euclideanBall_ne_top z hR.le)]

end PDE
