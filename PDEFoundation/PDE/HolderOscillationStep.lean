module

public import PDEFoundation.PDE.HolderReplacement
public import PDEFoundation.PDE.HarmonicGradientOscillation
public import PDEFoundation.Sobolev.H1.OscillationComparison

/-! # One-step gradient oscillation estimate for Hölder data -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Freezing Hölder coefficients at the center and taking the harmonic
replacement yields the exact half-scale oscillation step. -/
theorem centeredVectorMeanL2_half_le_of_holder [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R α Ka KF : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    {a : CoeffField d} {F : Vec d → Vec d}
    (ha : EuclideanMatrixHolderSeminormLE (euclideanBall z R) a α Ka)
    (hF : EuclideanFieldHolderSeminormLE (euclideanBall z R) F α KF)
    (ha0 : a z = 1) (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F) :
    centeredVectorMeanL2 (euclideanBall z (R / 2)) u.grad ≤
      (1 / 2 : ℝ) * centeredVectorMeanL2 (euclideanBall z R) u.grad +
        ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α *
          (Ka * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) + KF) := by
  obtain ⟨h, w, _hvalue, hgrad, hharm, hwbound⟩ :=
    exists_holderHarmonicReplacement_on_euclideanBall
      (by omega : 0 < d) hR hα hKa hKF ha hF ha0 u hsol
  have hhalf : 0 < R / 2 := by positivity
  have hsub : euclideanBall z (R / 2) ⊆ euclideanBall z R :=
    euclideanBall_mono hhalf.le (by linarith)
  have hdecay : centeredVectorMeanL2 (euclideanBall z (R / 2)) h.grad ≤
      (1 / 2 : ℝ) * centeredVectorMeanL2 (euclideanBall z R) h.grad := by
    have hraw := centeredVectorMeanL2_weakHarmonic_grad_decay hd hR h hharm
      hhalf (by linarith : R / 2 ≤ R) le_rfl
    convert hraw using 1
    field_simp
  have hcomp := centeredVectorMeanL2_comparison_of_contraction hsub
    h.gradMemL2 w.toH1Function.gradMemL2
    (volume_euclideanBall_pos z hhalf)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hhalf.le))
    (volume_euclideanBall_pos z hR)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hdecay
  have hsum : (fun x => h.grad x + w.toH1Function.grad x) = u.grad := by
    rw [hgrad]
    funext x
    ext i
    simp
  rw [hsum] at hcomp
  have hratio : Real.sqrt ((volume (euclideanBall z R)).toReal /
      (volume (euclideanBall z (R / 2))).toReal) =
      (2 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_div ENNReal.toReal_nonneg]
    exact sqrt_volume_euclideanBall_div_half z hR
  rw [hratio] at hcomp
  have hc : 0 ≤ (1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have herr := mul_le_mul_of_nonneg_left hwbound hc
  calc
    _ ≤ (1 / 2 : ℝ) * centeredVectorMeanL2 (euclideanBall z R) u.grad +
        ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2)) *
          Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (w.toH1Function.grad x))) := hcomp
    _ ≤ (1 / 2 : ℝ) * centeredVectorMeanL2 (euclideanBall z R) u.grad +
        ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / 2)) *
          (R ^ α * (Ka * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) + KF)) := add_le_add le_rfl herr
    _ = _ := by ring

end

end PDE
