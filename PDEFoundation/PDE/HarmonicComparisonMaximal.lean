module

public import PDEFoundation.PDE.LaplacianOscillationRetainedInterval
public import PDEFoundation.Measure.BallMaximalAverage

/-! # Harmonic comparison with the actual quadratic maximal function -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- Actual maximal domination discharges the uniform forcing bound only on
the radii used in the finite comparison, all of which are at least `r`. -/
theorem centeredVectorMeanL2_weakLaplacian_retained_maximal
    {d : ℕ} (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall z R) u 0 F)
    {θ r : ℝ} (hθ : 0 < θ) (hθone : θ < 1)
    (hr : 0 < r) (hrR : r ≤ R) {x : Vec d} (hx : x ∈ euclideanBall z r) :
    ENNReal.ofReal (centeredVectorMeanL2 (euclideanBall z r) u.grad) ≤
      ENNReal.ofReal ((r / R) * centeredVectorMeanL2 (euclideanBall z R) u.grad) +
        ENNReal.ofReal (θ ^ (-(d : ℝ) / 2) / (1 - θ)) * quadraticBallMaximal F x := by
  have hC : 0 < θ ^ (-(d : ℝ) / 2) / (1 - θ) :=
    div_pos (Real.rpow_pos_of_pos hθ _) (sub_pos.mpr hθone)
  by_cases htop : quadraticBallMaximal F x = ∞
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne', add_top]
    exact le_top
  · have hbound (b : ℝ) (hrb : r ≤ b) (hbR : b ≤ R) :
        Real.sqrt (integralAverage (euclideanBall z b) (fun y => vecNormSq (F y))) ≤
          (quadraticBallMaximal F x).toReal := by
      have hb : 0 < b := hr.trans_le hrb
      have hFb : MemVectorL2On (euclideanBall z b) F := fun i =>
        memLpOn_mono (euclideanBall_mono hb.le hbR) (hF i)
      have hxb : x ∈ euclideanBall z b := (euclideanBall_mono hr.le hrb) hx
      exact (ENNReal.ofReal_le_iff_le_toReal htop).1
        (ofReal_sqrt_integralAverage_vecNormSq_le_quadraticBallMaximal hb hFb hxb)
    have h := centeredVectorMeanL2_weakLaplacian_retained_of_forcing_bound_on_Icc
      hd hR u hF hsol ENNReal.toReal_nonneg hθ hθone hbound hr hrR
    have hbase : 0 ≤ (r / R) * centeredVectorMeanL2 (euclideanBall z R) u.grad :=
      mul_nonneg (div_nonneg hr.le hR.le) (Real.sqrt_nonneg _)
    have hproduct : θ ^ (-(d : ℝ) / 2) * (quadraticBallMaximal F x).toReal / (1 - θ) =
        (θ ^ (-(d : ℝ) / 2) / (1 - θ)) * (quadraticBallMaximal F x).toReal := by ring
    have he := ENNReal.ofReal_le_ofReal h
    rw [hproduct, ENNReal.ofReal_add hbase (mul_nonneg hC.le ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal htop] at he
    exact he

/-- The manuscript's choice of radius ratio gives its exact explicit harmonic
comparison constant. -/
theorem harmonicComparison_radius_constant {d : ℕ} (hd : 0 < d) :
    ((d : ℝ) / ((d : ℝ) + 2)) ^ (-(d : ℝ) / 2) /
        (1 - (d : ℝ) / ((d : ℝ) + 2)) =
      ((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2) := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hratio : ((d : ℝ) / ((d : ℝ) + 2))⁻¹ = 1 + 2 / (d : ℝ) := by
    field_simp
  have hden : 1 - (d : ℝ) / ((d : ℝ) + 2) = 2 / ((d : ℝ) + 2) := by
    field_simp
    ring
  rw [neg_div, Real.rpow_neg_eq_inv_rpow, hratio, hden]
  field_simp

/-- The retained-excess harmonic comparison, with the exact manuscript
constant and the literal quadratic maximal function of any extension of `F`. -/
theorem centeredVectorMeanL2_weakLaplacian_retained_excess
    {d : ℕ} (hd : 0 < d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
      (euclideanBall z R) u 0 F)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) {x : Vec d} (hx : x ∈ euclideanBall z r) :
    ENNReal.ofReal (centeredVectorMeanL2 (euclideanBall z r) u.grad) ≤
      ENNReal.ofReal ((r / R) * centeredVectorMeanL2 (euclideanBall z R) u.grad) +
        ENNReal.ofReal (((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)) *
          quadraticBallMaximal F x := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hθ : 0 < (d : ℝ) / ((d : ℝ) + 2) := div_pos hdR (by positivity)
  have hθone : (d : ℝ) / ((d : ℝ) + 2) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have h := centeredVectorMeanL2_weakLaplacian_retained_maximal
    hd hR u hF hsol hθ hθone hr hrR hx
  rwa [harmonicComparison_radius_constant hd] at h

end PDE
