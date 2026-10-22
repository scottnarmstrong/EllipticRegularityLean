module

public import PDEFoundation.PDE.HolderOscillationStep
public import PDEFoundation.Analysis.DyadicOscillationWeights

/-! # Weighted dyadic oscillation recurrence for Hölder data -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The actual half-scale replacement estimate, weighted by the Campanato
factor at consecutive dyadic radii. -/
theorem holder_weighted_dyadic_oscillation_step [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R α Ka KF : ℝ}
    (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    {a : CoeffField d} {F : Vec d → Vec d}
    (ha : EuclideanMatrixHolderSeminormLE (euclideanBall z R) a α Ka)
    (hF : EuclideanFieldHolderSeminormLE (euclideanBall z R) F α KF)
    (ha0 : a z = 1) (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (n : ℕ) :
      (R / dyadicRadius R (n + 1)) ^ α *
          centeredVectorMeanL2 (euclideanBall z (dyadicRadius R (n + 1))) u.grad ≤
        (2 : ℝ) ^ (α - 1) *
          ((R / dyadicRadius R n) ^ α *
            centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) u.grad) +
        (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α *
          (Ka * Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
            (fun x => vecNormSq (u.grad x))) + KF) := by
  let rn := dyadicRadius R n
  have hrn : 0 < rn := dyadicRadius_pos hR n
  have hrnR : rn ≤ R := dyadicRadius_le hR.le n
  have hsub : euclideanBall z rn ⊆ euclideanBall z R :=
    euclideanBall_mono hrn.le hrnR
  let un : H1Function (euclideanBall z rn) :=
    u.restrict (isOpen_euclideanBall z rn) hsub
  have hsoln : IsWeakDivergenceFormSolutionOn a (euclideanBall z rn) un 0 F :=
    hsol.restrict (isOpen_euclideanBall z R) (isOpen_euclideanBall z rn) hsub
  have han : EuclideanMatrixHolderSeminormLE (euclideanBall z rn) a α Ka :=
    fun x hx y hy v => ha x (hsub hx) y (hsub hy) v
  have hFn : EuclideanFieldHolderSeminormLE (euclideanBall z rn) F α KF :=
    hF.mono_set hsub
  have hstep := centeredVectorMeanL2_half_le_of_holder hd hrn hα0 hKa hKF
    han hFn ha0 un hsoln
  rw [← dyadicRadius_succ R n] at hstep
  simp only [un, H1Function.restrict_grad] at hstep
  let wn : ℝ := (R / dyadicRadius R n) ^ α
  let ws : ℝ := (R / dyadicRadius R (n + 1)) ^ α
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  let X : ℝ := Ka * Real.sqrt (integralAverage (euclideanBall z rn)
    (fun x => vecNormSq (u.grad x))) + KF
  have hws : 0 ≤ ws := Real.rpow_nonneg
    (div_nonneg hR.le (dyadicRadius_pos hR (n + 1)).le) _
  have hX : 0 ≤ X := add_nonneg
    (mul_nonneg hKa (Real.sqrt_nonneg _)) hKF
  have hmul := mul_le_mul_of_nonneg_left hstep hws
  have hweight : ws = (2 : ℝ) ^ α * wn := by
    exact div_dyadicRadius_succ_rpow_eq hR α n
  have hscale : ws * rn ^ α = (2 : ℝ) ^ α * R ^ α :=
    div_dyadicRadius_succ_rpow_mul_current_rpow hR α n
  have hcontract : ws * ((1 / 2 : ℝ) *
      centeredVectorMeanL2 (euclideanBall z rn) u.grad) =
      (2 : ℝ) ^ (α - 1) *
        (wn * centeredVectorMeanL2 (euclideanBall z rn) u.grad) := by
    rw [hweight, Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    field_simp
    ring
  have htwoα : (2 : ℝ) ^ α ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1.le
    simpa only [Real.rpow_one] using this
  have hcoef : (2 : ℝ) ^ α * ((1 / 2 : ℝ) + D) ≤ 1 + 2 * D := by
    have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
    calc
      _ ≤ 2 * ((1 / 2 : ℝ) + D) :=
        mul_le_mul_of_nonneg_right htwoα (add_nonneg (by norm_num) hD)
      _ = _ := by ring
  change ws * centeredVectorMeanL2
      (euclideanBall z (dyadicRadius R (n + 1))) u.grad ≤ _
  dsimp only [rn, wn, ws, D, X] at hmul hcontract hscale hcoef ⊢
  calc
    _ ≤ ws * ((1 / 2 : ℝ) * centeredVectorMeanL2
          (euclideanBall z (dyadicRadius R n)) u.grad +
        ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2)) *
          dyadicRadius R n ^ α *
          (Ka * Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
            (fun x => vecNormSq (u.grad x))) + KF)) := hmul
    _ = (2 : ℝ) ^ (α - 1) *
          ((R / dyadicRadius R n) ^ α * centeredVectorMeanL2
            (euclideanBall z (dyadicRadius R n)) u.grad) +
        ((2 : ℝ) ^ α * ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2))) * R ^ α *
          (Ka * Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
            (fun x => vecNormSq (u.grad x))) + KF) := by
      rw [mul_add, hcontract]
      congr 1
      calc
        ws * (((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2)) *
            dyadicRadius R n ^ α *
              (Ka * Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
                (fun x => vecNormSq (u.grad x))) + KF)) =
            ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2)) *
              (ws * dyadicRadius R n ^ α) *
                (Ka * Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
                  (fun x => vecNormSq (u.grad x))) + KF) := by ring
        _ = _ := by rw [hscale]; ring
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hR.le α)) hX)

end

end PDE
