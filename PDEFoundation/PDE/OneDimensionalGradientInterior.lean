module

public import PDEFoundation.PDE.OneDimensionalGradientMean
public import PDEFoundation.PDE.OneDimensionalGradientHolder

/-! # Interior one-dimensional gradient representative bounds -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem sqrt_volume_unitBall_div_ball_eq_rpow_neg_half
    (x : Vec 1) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (volume (euclideanBall (0 : Vec 1) 1)).toReal /
        Real.sqrt (volume (euclideanBall x r)).toReal = r ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.sqrt_div ENNReal.toReal_nonneg,
    volume_euclideanBall_toReal_div_eq_div_pow (0 : Vec 1) x hr (by norm_num)]
  norm_num
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_neg hr.le _).symm

/-- The one-dimensional weak equation produces an interior continuous
gradient representative with quantitative pointwise and Hölder bounds. -/
theorem exists_oneDimensional_gradient_interior_representative
    {a : CoeffField 1} {F : Vec 1 → Vec 1}
    {r₀ alpha Ka KF Lam : ℝ}
    (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    (halpha : 0 < alpha) (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    (ha : EuclideanMatrixHolderSeminormLE
      (euclideanBall (0 : Vec 1) 1) a alpha Ka)
    (hF : EuclideanFieldHolderSeminormLE
      (euclideanBall (0 : Vec 1) 1) F alpha KF)
    (hell : ∀ x ∈ euclideanBall (0 : Vec 1) 1,
      IsEllipticMatrix 1 Lam (a x))
    (u : H1Function (euclideanBall (0 : Vec 1) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec 1) 1) u 0 F) :
    let B := Lam * r₀ ^ (-(1 / 2 : ℝ)) *
        Real.sqrt (integralAverage (euclideanBall (0 : Vec 1) 1)
          (fun x => vecNormSq (u.grad x))) + KF * r₀ ^ alpha
    ∃ G : Vec 1 → Vec 1,
      G =ᵐ[volumeOn (euclideanBall (0 : Vec 1) (1 / 2))] u.grad ∧
      (∀ x ∈ euclideanBall (0 : Vec 1) (1 / 2), vecEuclideanNorm (G x) ≤ B) ∧
      EuclideanFieldHolderSeminormLE
        (euclideanBall (0 : Vec 1) (1 / 2)) G alpha (KF + Ka * B) := by
  dsimp only
  obtain ⟨c, G, _hformula, hGae, _hGcont, hflux⟩ :=
    exists_oneDimensional_gradient_quotient_representative
      halpha hKa hKF ha hF hell u hsol
  have hhalfsub : euclideanBall (0 : Vec 1) (1 / 2) ⊆
      euclideanBall (0 : Vec 1) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hGaeHalf : G =ᵐ[volumeOn (euclideanBall (0 : Vec 1) (1 / 2))] u.grad :=
    hGae.filter_mono (ae_mono (Measure.restrict_mono hhalfsub le_rfl))
  have hlocalEnergy : ∀ x ∈ euclideanBall (0 : Vec 1) (1 / 2),
      Real.sqrt (integralAverage (euclideanBall x r₀)
        (fun y => vecNormSq (u.grad y))) ≤
      r₀ ^ (-(1 / 2 : ℝ)) *
        Real.sqrt (integralAverage (euclideanBall (0 : Vec 1) 1)
          (fun y => vecNormSq (u.grad y))) := by
    intro x hx
    have hsub : euclideanBall x r₀ ⊆ euclideanBall (0 : Vec 1) 1 := by
      have hrhalf : r₀ ≤ 1 / 2 := hr₀le.trans (by norm_num)
      exact (euclideanBall_mono hr₀.le hrhalf).trans
        (euclideanBall_half_subset_unit_of_center_mem_half hx)
    have hmono := sqrt_integralAverage_vecNormSq_mono_set hsub
      (volume_euclideanBall_toReal_pos (0 : Vec 1) (by norm_num)) u.gradMemL2
    rw [sqrt_volume_unitBall_div_ball_eq_rpow_neg_half x hr₀] at hmono
    exact hmono
  have hpoint : ∀ x ∈ euclideanBall (0 : Vec 1) (1 / 2),
      vecEuclideanNorm (G x) ≤
        Lam * r₀ ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec 1) 1)
            (fun y => vecNormSq (u.grad y))) + KF * r₀ ^ alpha := by
    intro x hx
    have hp := vecEuclideanNorm_oneDimensional_gradient_le_of_constant_flux
      halpha hKa hKF ha hF hell hGae hflux x hx r₀ hr₀
        (hr₀le.trans (by norm_num))
    have he := mul_le_mul_of_nonneg_left (hlocalEnergy x hx)
      (hell x (hhalfsub hx)).Lam_pos.le
    calc
      _ ≤ Lam * Real.sqrt (integralAverage (euclideanBall x r₀)
          (fun y => vecNormSq (u.grad y))) + KF * r₀ ^ alpha := hp
      _ ≤ Lam * (r₀ ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec 1) 1)
            (fun y => vecNormSq (u.grad y)))) + KF * r₀ ^ alpha :=
        add_le_add he le_rfl
      _ = _ := by ring
  refine ⟨G, hGaeHalf, hpoint, ?_⟩
  exact oneDimensional_gradient_holder_of_constantFlux hKa hKF
    (add_nonneg
      (mul_nonneg (mul_nonneg (hell 0 (center_mem_euclideanBall _ (by norm_num))).Lam_pos.le
        (Real.rpow_nonneg hr₀.le _)) (Real.sqrt_nonneg _))
      (mul_nonneg hKF (Real.rpow_nonneg hr₀.le _)))
    (fun x hx y hy v => ha x (hhalfsub hx) y (hhalfsub hy) v)
    (hF.mono_set hhalfsub) (fun x hx => hell x (hhalfsub hx))
    (fun x hx => hflux x (hhalfsub hx)) hpoint

end

end PDE
