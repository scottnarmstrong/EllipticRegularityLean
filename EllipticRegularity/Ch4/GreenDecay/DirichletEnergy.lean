module

public import EllipticRegularity.Ch4.GreenDecay.Dirichlet

/-!
# The Dirichlet problem on `B_R`: coercivity, uniqueness and energy bounds

For an elliptic field `b` (`IsEllipticMatrix 1 Λ`) on `B_R`, testing the equation with the solution
gives the energy identity; coercivity and the Poincaré inequality (constant `2R`) yield uniqueness and
the bounds `‖∇v‖ ≤ 2R ‖g‖`, `‖v‖ ≤ 4R² ‖g‖` when the forcing vanishes.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.MeyersDuality

noncomputable section

variable {d : ℕ}

section Coercive

variable {Λ R : ℝ} {b : CoeffField d}

/-- Coercivity of the flux form on an elliptic field. -/
theorem integral_vecNormSq_le_flux {U : Set (Vec d)} (hUm : MeasurableSet U)
    (hbm : ∀ i j : Fin d, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hbell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (b x)) (u : H1Function U) :
    (∫ x in U, vecNormSq (u.grad x)) ≤
      ∫ x in U, vecDot (matVecMul (b x) (u.grad x)) (u.grad x) := by
  have hflux := memVectorL2On_matVecMul_of_ae_elliptic hUm hbm hbell u.gradMemL2
  apply integral_mono_ae (integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2)
    (integrableOn_vecDot_of_memVectorL2On hflux u.gradMemL2)
  have hmem : ∀ᵐ x ∂ volumeOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff' hUm).2 (Filter.Eventually.of_forall fun x hx => hx)
  filter_upwards [hmem] with x hx
  have := (hbell x hx).coercive (u.grad x)
  rw [one_mul, vecDot_comm] at this
  exact this

end Coercive

section Ball

variable {Λ R : ℝ} {b : CoeffField d} {g : Vec d → ℝ} {F : Vec d → Vec d}

/-- Uniqueness of `H¹₀(U)` solutions (value and gradient almost everywhere), given a Poincaré
inequality on `H¹₀(U)`. -/
theorem dirichlet_unique_of_poincare {U : Set (Vec d)} (hUm : MeasurableSet U) {P : ℝ}
    (hP : ∀ u : H10Function U, (∫ x in U, u.toH1Function.toFun x ^ 2) ≤
      P * ∫ x in U, vecNormSq (u.toH1Function.grad x))
    (hbm : ∀ i j : Fin d, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hbell : ∀ x ∈ U, IsEllipticMatrix 1 Λ (b x))
    {v w : H10Function U}
    (hv : IsWeakDivergenceFormH10SolutionOn b U v.toH1Function g F)
    (hw : IsWeakDivergenceFormH10SolutionOn b U w.toH1Function g F) :
    v.toH1Function.toFun =ᵐ[volumeOn U] w.toH1Function.toFun ∧
      v.toH1Function.grad =ᵐ[volumeOn U] w.toH1Function.grad := by
  let u : H10Function U := PDE.Ch4Infra.h10Sub v w
  have hufl := memVectorL2On_matVecMul_of_ae_elliptic hUm hbm hbell u.toH1Function.gradMemL2
  have hvfl := memVectorL2On_matVecMul_of_ae_elliptic hUm hbm hbell v.toH1Function.gradMemL2
  have hwfl := memVectorL2On_matVecMul_of_ae_elliptic hUm hbm hbell w.toH1Function.gradMemL2
  have i1 := integrableOn_vecDot_of_memVectorL2On hvfl u.toH1Function.gradMemL2
  have i2 := integrableOn_vecDot_of_memVectorL2On hwfl u.toH1Function.gradMemL2
  have hzero : (∫ x in U, vecDot (matVecMul (b x) (u.toH1Function.grad x))
      (u.toH1Function.grad x)) = 0 := by
    have e1 := (hv u).2
    have e2 := (hw u).2
    have hpt : ∀ x, vecDot (matVecMul (b x) (u.toH1Function.grad x)) (u.toH1Function.grad x) =
        vecDot (matVecMul (b x) (v.toH1Function.grad x)) (u.toH1Function.grad x) -
        vecDot (matVecMul (b x) (w.toH1Function.grad x)) (u.toH1Function.grad x) := by
      intro x
      change vecDot (matVecMul (b x) (v.toH1Function.grad x - w.toH1Function.grad x))
        (u.toH1Function.grad x) = _
      rw [matVecMul_sub_right', vecDot_sub_left']
    simp_rw [hpt]
    rw [integral_sub i1 i2, e1, e2]
    ring
  have hle := integral_vecNormSq_le_flux hUm hbm hbell u.toH1Function
  rw [hzero] at hle
  have hnn : 0 ≤ ∫ x in U, vecNormSq (u.toH1Function.grad x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hint0 : (∫ x in U, vecNormSq (u.toH1Function.grad x)) = 0 := le_antisymm hle hnn
  have hae : (fun x => vecNormSq (u.toH1Function.grad x)) =ᵐ[volumeOn U] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => vecNormSq_nonneg _)
      (integrableOn_vecNormSq_of_memVectorL2On u.toH1Function.gradMemL2)).1 hint0
  have hpoinc := hP u
  rw [hint0, mul_zero] at hpoinc
  have hu2 : (∫ x in U, u.toH1Function.toFun x ^ 2) = 0 :=
    le_antisymm hpoinc (integral_nonneg fun x => sq_nonneg _)
  have hu2ae : (fun x => u.toH1Function.toFun x ^ 2) =ᵐ[volumeOn U] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (u.toH1Function.memL2.integrable_sq)).1 hu2
  refine ⟨?_, ?_⟩
  · filter_upwards [hu2ae] with x hx
    have hx' : (v.toH1Function.toFun x - w.toH1Function.toFun x) ^ 2 = 0 := hx
    have := (pow_eq_zero_iff (two_ne_zero)).1 hx'
    linarith
  · filter_upwards [hae] with x hx
    have hx' : vecNormSq (v.toH1Function.grad x - w.toH1Function.grad x) = 0 := hx
    have := vecNormSq_eq_zero_iff.1 hx'
    exact sub_eq_zero.1 this

/-- Uniqueness of `H¹₀(B_R)` solutions (value and gradient almost everywhere). -/
theorem dirichlet_unique (hd : 0 < d) (hR : 0 < R)
    (hbm : ∀ i j : Fin d,
      AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x))
    {v w : H10Function (euclideanBall (0 : Vec d) R)}
    (hv : IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F)
    (hw : IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) w.toH1Function g F) :
    v.toH1Function.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] w.toH1Function.toFun ∧
      v.toH1Function.grad =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] w.toH1Function.grad :=
  dirichlet_unique_of_poincare (measurableSet_euclideanBall _ _)
    (fun u => h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_vecNormSq_grad_on_euclideanBall
      hd hR u) hbm hbell hv hw

/-- **Energy bounds** for the `H¹₀(B_R)` solution with vanishing forcing: with `C₁ = 2`,
`‖∇v‖ ≤ C₁ R ‖g‖` and `‖v‖ ≤ C₁² R² ‖g‖`. -/
theorem dirichlet_energy_bounds (hd : 0 < d) (hR : 0 < R)
    (hbm : ∀ i j : Fin d,
      AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x))
    (hg : MemL2On (euclideanBall (0 : Vec d) R) g)
    {v : H10Function (euclideanBall (0 : Vec d) R)}
    (hv : IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g
      (0 : Vec d → Vec d)) :
    eLpNorm (fun x => vecEuclideanNorm (v.toH1Function.grad x)) 2
        (volumeOn (euclideanBall (0 : Vec d) R)) ≤
      ENNReal.ofReal (2 * R) * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) ∧
    eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≤
      ENNReal.ofReal (2 ^ 2 * R ^ 2) * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) := by
  have hUm : MeasurableSet (euclideanBall (0 : Vec d) R) := measurableSet_euclideanBall _ _
  have hgrad : MemL2On (euclideanBall (0 : Vec d) R)
      (fun x => vecEuclideanNorm (v.toH1Function.grad x)) :=
    GradMemLpOn.memLp_vecEuclideanNorm v.toH1Function.gradMemL2
  have hvL : MemL2On (euclideanBall (0 : Vec d) R) v.toH1Function.toFun := v.toH1Function.memL2
  set a := (eLpNorm (fun x => vecEuclideanNorm (v.toH1Function.grad x)) 2
    (volumeOn (euclideanBall (0 : Vec d) R))).toReal with ha
  set m := (eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal
    with hm
  set n := (eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal with hn
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hn0 : 0 ≤ n := ENNReal.toReal_nonneg
  have hA : a ^ 2 = ∫ x in euclideanBall (0 : Vec d) R, vecNormSq (v.toH1Function.grad x) := by
    rw [ha, toReal_eLpNorm_sq hgrad]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecEuclideanNorm_sq' _)
  have hB : m ^ 2 = ∫ x in euclideanBall (0 : Vec d) R, v.toH1Function.toFun x ^ 2 := by
    rw [hm, toReal_eLpNorm_sq hvL]
  have hpoinc :=
    h10_setIntegral_sq_le_four_mul_radius_sq_setIntegral_vecNormSq_grad_on_euclideanBall
      hd hR v
  -- the energy identity
  have hcoerc := integral_vecNormSq_le_flux hUm hbm hbell v.toH1Function
  have hself := (hv v).2
  simp only [Pi.zero_apply, vecDot, zero_mul, Finset.sum_const_zero, integral_zero,
    sub_zero] at hself
  have hself' : (∫ x in euclideanBall (0 : Vec d) R,
      vecDot (matVecMul (b x) (v.toH1Function.grad x)) (v.toH1Function.grad x)) =
      ∫ x in euclideanBall (0 : Vec d) R, g x * v.toH1Function.toFun x := hself
  have hcs : (∫ x in euclideanBall (0 : Vec d) R, g x * v.toH1Function.toFun x) ≤ n * m := by
    rw [integral_mul_eq_inner hg hvL.toScalarLp hvL.coeFn_toScalarLp]
    refine (real_inner_le_norm _ _).trans ?_
    have e1 : ‖hg.toScalarLp‖ = n := Lp.norm_toLp g hg
    have e2 : ‖hvL.toScalarLp‖ = m := Lp.norm_toLp _ hvL
    rw [e1, e2]
  have h1 : a ^ 2 ≤ n * m := by
    rw [hA]; exact hcoerc.trans (hself'.le.trans hcs)
  have h2 : m ^ 2 ≤ (2 * R) ^ 2 * a ^ 2 := by
    rw [hA, hB]; exact hpoinc
  have hR2 : 0 ≤ 2 * R := by linarith
  have h3 : m ≤ 2 * R * a := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hR2 ha0]
  have h4 : a ≤ 2 * R * n := by
    rcases eq_or_lt_of_le ha0 with h | h
    · rw [← h]; exact mul_nonneg hR2 hn0
    · by_contra hcon
      push Not at hcon
      nlinarith [mul_le_mul_of_nonneg_left h3 hn0]
  have h5 : m ≤ 2 ^ 2 * R ^ 2 * n := by nlinarith [mul_le_mul_of_nonneg_left h4 hR2]
  have hfin1 : eLpNorm (fun x => vecEuclideanNorm (v.toH1Function.grad x)) 2
      (volumeOn (euclideanBall (0 : Vec d) R)) ≠ ⊤ := hgrad.eLpNorm_ne_top
  have hfin2 : eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≠ ⊤ :=
    hvL.eLpNorm_ne_top
  have hfin3 : eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≠ ⊤ := hg.eLpNorm_ne_top
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin3,
      ← ENNReal.ofReal_mul hR2]
    exact ENNReal.ofReal_le_ofReal h4
  · rw [← ENNReal.ofReal_toReal hfin2, ← ENNReal.ofReal_toReal hfin3,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h5

end Ball

end

end PDE.Ch4GreenDecay
