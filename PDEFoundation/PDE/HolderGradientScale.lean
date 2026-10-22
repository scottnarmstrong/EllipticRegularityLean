module

public import PDEFoundation.PDE.HolderDyadicOscillation
public import PDEFoundation.Sobolev.H1.DyadicOscillationReadout

/-! # Arbitrary-scale gradient bounds for Hölder data -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The finite dyadic Schauder iteration read at every intermediate positive
radius. -/
theorem holder_gradient_scale_bound [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R α Ka KF : ℝ}
    (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    {a : CoeffField d} {F : Vec d → Vec d}
    (ha : EuclideanMatrixHolderSeminormLE (euclideanBall z R) a α Ka)
    (hF : EuclideanFieldHolderSeminormLE (euclideanBall z R) F α KF)
    (ha0 : a z = 1) (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (hsmall : (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α * Ka ≤
      α * (1 - α) / (32 * (1 + (2 : ℝ) ^ ((d : ℝ) / 2)))) :
    ∀ r : ℝ, 0 < r → r ≤ R →
      Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x))) ≤
        (40 * (2 : ℝ) ^ ((d : ℝ) / 2) *
          (1 + (2 : ℝ) ^ ((d : ℝ) / 2)) / α) *
          (2 * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) +
            (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α * KF / (1 - α)) ∧
      (R / r) ^ α * centeredVectorMeanL2 (euclideanBall z r) u.grad ≤
        16 * (2 : ℝ) ^ ((d : ℝ) / 2) *
          (2 * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) +
            (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α * KF / (1 - α)) := by
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  let H : ℝ := 1 + 2 * D
  let M0 : ℝ := Real.sqrt (integralAverage (euclideanBall z R)
    (fun x => vecNormSq (u.grad x)))
  let Q : ℝ := 2 * M0 + H * R ^ α * KF / (1 - α)
  let A : ℝ := 8 * Q
  let B : ℝ := (40 * (1 + D) / α) * Q
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hH : 0 ≤ H := add_nonneg (by norm_num) (mul_nonneg (by norm_num) hD)
  have hgap : 0 < 1 - α := sub_pos.mpr hα1
  have hQ : 0 ≤ Q := by
    dsimp only [Q, M0, H]
    exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg (mul_nonneg hH (Real.rpow_nonneg hR.le _)) hKF) hgap.le)
  have hA : 0 ≤ A := mul_nonneg (by norm_num) hQ
  have hB : 0 ≤ B := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (add_nonneg (by norm_num) hD)) hα0.le) hQ
  have hfinite := holder_dyadic_oscillation_bound hd hR hα0 hα1 hKa hKF
    ha hF ha0 u hsol hsmall
  have hosc : ∀ n : ℕ,
      (R / dyadicRadius R n) ^ α *
        centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) u.grad ≤ A := by
    intro n
    simpa only [A, Q, M0, D, H] using (hfinite n).1
  have henergy : ∀ n : ℕ,
      Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
        (fun x => vecNormSq (u.grad x))) ≤ B := by
    intro n
    simpa only [B, Q, M0, D, H] using (hfinite n).2
  have hread := dyadic_vector_bounds_readout hR hα0 hα1 hA hB
    u.gradMemL2 hosc henergy
  intro r hr hrR
  have hrb := hread r hr hrR
  dsimp only [dyadicBallReadoutCoefficient, B, A, Q, M0, D, H] at hrb ⊢
  constructor
  · exact hrb.1.trans_eq (by ring)
  · exact hrb.2.trans_eq (by ring)

end

end PDE
