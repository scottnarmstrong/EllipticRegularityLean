module

public import PDEFoundation.Measure.BallMaximal
public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.Mean

/-! # Literal real averages and the extended ball maximal function -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- Positive finite-volume ball averages agree exactly in real and extended
nonnegative integral conventions. -/
theorem ofReal_integralAverage_abs_eq_lintegralAverage
    {d : ℕ} (b : Vec d → ℝ) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hb : IntegrableOn b (euclideanBall z R)) :
    ENNReal.ofReal (integralAverage (euclideanBall z R) (fun y => |b y|)) =
      (volume (euclideanBall z R))⁻¹ *
        ∫⁻ y in euclideanBall z R, ENNReal.ofReal |b y| := by
  rw [integralAverage, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos (volume_euclideanBall_toReal_pos z hR),
    ENNReal.ofReal_toReal (volume_euclideanBall_ne_top z hR.le),
    ofReal_integral_eq_lintegral_ofReal hb.abs (ae_of_all _ (fun y => abs_nonneg (b y)))]

theorem ofReal_integralAverage_abs_le_uncenteredBallMaximal
    {d : ℕ} (b : Vec d → ℝ) {x z : Vec d} {R : ℝ} (hR : 0 < R)
    (hb : IntegrableOn b (euclideanBall z R)) (hx : x ∈ euclideanBall z R) :
    ENNReal.ofReal (integralAverage (euclideanBall z R) (fun y => |b y|)) ≤
      uncenteredBallMaximal b x := by
  rw [ofReal_integralAverage_abs_eq_lintegralAverage b hR hb]
  exact lintegralAverage_le_uncenteredBallMaximal b hR hx

/-- The normalized Euclidean forcing RMS on any ball containing the point is
bounded by the literal quadratic maximal function, even when it is infinite. -/
theorem ofReal_sqrt_integralAverage_vecNormSq_le_quadraticBallMaximal
    {d : ℕ} {F : Vec d → Vec d} {x z : Vec d} {R : ℝ} (hR : 0 < R)
    (hF : MemVectorL2On (euclideanBall z R) F) (hx : x ∈ euclideanBall z R) :
    ENNReal.ofReal (Real.sqrt (integralAverage (euclideanBall z R)
      (fun y => vecNormSq (F y)))) ≤ quadraticBallMaximal F x := by
  have h := ofReal_integralAverage_abs_le_uncenteredBallMaximal
    (fun y => vecNormSq (F y)) hR (integrableOn_vecNormSq_of_memVectorL2On hF) hx
  simp only [abs_of_nonneg (vecNormSq_nonneg _)] at h
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg
    (integralAverage_nonneg (isOpen_euclideanBall z R).measurableSet
      (fun y _ => vecNormSq_nonneg (F y))) (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

end PDE
