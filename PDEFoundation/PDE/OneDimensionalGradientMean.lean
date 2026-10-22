module

public import PDEFoundation.PDE.OneDimensionalGradientRepresentative
public import PDEFoundation.Regularity.HolderBallBounds
public import PDEFoundation.Sobolev.H1.MeanEnergyOperator
public import PDEFoundation.Sobolev.H1.MeanEnergyTriangle
public import PDEFoundation.Sobolev.H1.VectorMeanRestriction
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Local mean control of a one-dimensional constant-flux gradient -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem oneDimensional_diag_lower'
    {Lam : ℝ} {A : Mat 1} (hA : IsEllipticMatrix 1 Lam A) : 1 ≤ A 0 0 := by
  have h := hA.coercive (basisVec 0)
  norm_num [vecNormSq, vecDot, matVecMul, basisVec] at h ⊢
  exact h

/-- Local pointwise control of a one-dimensional gradient representative,
given the constant-flux identity produced by the weak equation. -/
theorem vecEuclideanNorm_oneDimensional_gradient_le_of_constant_flux
    {a : CoeffField 1} {F G : Vec 1 → Vec 1}
    {u : H1Function (euclideanBall (0 : Vec 1) 1)}
    {alpha Ka KF Lam c : ℝ}
    (halpha : 0 < alpha) (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    (ha : EuclideanMatrixHolderSeminormLE
      (euclideanBall (0 : Vec 1) 1) a alpha Ka)
    (hF : EuclideanFieldHolderSeminormLE
      (euclideanBall (0 : Vec 1) 1) F alpha KF)
    (hell : ∀ y ∈ euclideanBall (0 : Vec 1) 1,
      IsEllipticMatrix 1 Lam (a y))
    (hG : G =ᵐ[volumeOn (euclideanBall (0 : Vec 1) 1)] u.grad)
    (hflux : ∀ y ∈ euclideanBall (0 : Vec 1) 1,
      a y 0 0 * G y 0 + F y 0 = c) :
    ∀ x ∈ euclideanBall (0 : Vec 1) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ 1 / 2 →
      vecEuclideanNorm (G x) ≤
        Lam * Real.sqrt (integralAverage (euclideanBall x r)
          (fun y => vecNormSq (u.grad y))) + KF * r ^ alpha := by
  intro x hx r hr hrhalf
  let B := euclideanBall (0 : Vec 1) 1
  let V := euclideanBall x r
  have hVB : V ⊆ B := by
    exact (euclideanBall_mono hr.le hrhalf).trans
      (euclideanBall_half_subset_unit_of_center_mem_half hx)
  have hxB : x ∈ B := hVB (center_mem_euclideanBall x hr)
  have hVmeas : MeasurableSet V := (isOpen_euclideanBall _ _).measurableSet
  have hVpos : 0 < volume V := volume_euclideanBall_pos x hr
  have hVtop : volume V < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top x hr.le)
  let P : Vec 1 → Vec 1 := fun y => matVecMul (a y) (u.grad y)
  let Q : Vec 1 → Vec 1 := fun y => F y - F x
  have huV : MemVectorL2On V u.grad := fun i =>
    (u.gradMemL2 i).mono_measure (Measure.restrict_mono hVB le_rfl)
  have hmeas : ∀ i j, AEStronglyMeasurable (fun y => a y i j) (volumeOn V) := by
    intro i j
    exact (((ha.coordinate i j).continuousOn halpha hKa).mono hVB).aestronglyMeasurable hVmeas
  have hPbound : ∀ᵐ y ∂volumeOn V, ∀ v : Vec 1,
      vecEuclideanNorm (matVecMul (a y) v) ≤ Lam * vecEuclideanNorm v := by
    filter_upwards [ae_restrict_mem hVmeas] with y hy
    exact vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix (hell y (hVB hy))
  have hLam : 0 ≤ Lam := (hell x hxB).Lam_pos.le
  have hP : MemVectorL2On V P :=
    memVectorL2On_matVecMul_of_ae_operator_bound huV hmeas hLam hPbound
  have hQ : MemVectorL2On V Q :=
    hF.memVectorL2On_sub_center halpha hKF hr hxB hVB
  have hHae : (fun y => P y + Q y) =ᵐ[volumeOn V]
      (fun _ => fun _ => c - F x 0) := by
    filter_upwards [hG.filter_mono (ae_mono (Measure.restrict_mono hVB le_rfl)),
      ae_restrict_mem hVmeas] with y hGy hy
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hf := hflux y (hVB hy)
    change (matVecMul (a y) (u.grad y)) 0 + (F y - F x) 0 = c - F x 0
    rw [← hGy]
    simp only [Pi.sub_apply, matVecMul, Fin.sum_univ_one] at hf ⊢
    linarith
  have hmean : vectorIntegralAverage V (fun y => P y + Q y) =
      (fun _ => c - F x 0) := by
    funext i
    rw [vectorIntegralAverage_apply]
    have heq := hHae.fun_comp (fun z => z i)
    have heq' : (fun y => (P y + Q y) i) =ᵐ[volumeOn V]
        (fun _ => c - F x 0) := by
      simpa only [Function.comp_apply] using! heq
    rw [integralAverage_congr_ae heq']
    simpa using congrArg (fun z => z i)
      (vectorIntegralAverage_const hVpos hVtop (fun _ => c - F x 0))
  have havg : vecEuclideanNorm (vectorIntegralAverage V (fun y => P y + Q y)) ≤
      Real.sqrt (integralAverage V (fun y => vecNormSq (P y + Q y))) := by
    simpa only [Pi.add_apply] using!
      (vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq
        (U := V) (fun i => (hP i).add (hQ i)) hVpos hVtop)
  rw [hmean] at havg
  have htri := sqrt_integralAverage_vecNormSq_add_le hP hQ
  have hPbound' : ∀ᵐ y ∂volumeOn V,
      vecEuclideanNorm (P y) ≤ Lam * vecEuclideanNorm (u.grad y) := by
    filter_upwards [hPbound] with y hy
    exact hy (u.grad y)
  have hPop := sqrt_integralAverage_vecNormSq_le_mul_of_ae_vecEuclideanNorm_le
    hP huV hLam hPbound'
  have hQbound := hF.sqrt_mean_sub_center_le_of_pos halpha hKF hr hxB hVB
  have hconstant : vecEuclideanNorm (G x) ≤
      vecEuclideanNorm (fun _ : Fin 1 => c - F x 0) := by
    have ha1 := oneDimensional_diag_lower' (hell x hxB)
    have hf := hflux x hxB
    simp only [vecEuclideanNorm, vecNormSq, vecDot, Fin.sum_univ_one]
    simp only [← pow_two]
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    have : G x 0 = (c - F x 0) / a x 0 0 := by
      apply (eq_div_iff (ne_of_gt (lt_of_lt_of_le zero_lt_one ha1))).2
      linarith
    rw [this, abs_div]
    exact div_le_self (abs_nonneg _) (by simpa [abs_of_nonneg (zero_le_one.trans ha1)] using ha1)
  exact hconstant.trans (havg.trans (htri.trans (add_le_add hPop hQbound)))

end

end PDE
