module

public import PDEFoundation.PDE.OneDimensionalFlux
public import PDEFoundation.Regularity.HolderBallBounds
public import PDEFoundation.Geometry.ConvexDomain

/-! # One-dimensional gradient representatives from constant flux -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem oneDimensional_diag_lower
    {Lam : ℝ} {A : Mat 1} (hA : IsEllipticMatrix 1 Lam A) : 1 ≤ A 0 0 := by
  have h := hA.coercive (basisVec 0)
  norm_num [vecNormSq, vecDot, matVecMul, basisVec] at h ⊢
  exact h

/-- The one-dimensional weak equation supplies a continuous quotient
representative of the weak gradient through its actual constant flux. -/
theorem exists_oneDimensional_gradient_quotient_representative
    {a : CoeffField 1} {F : Vec 1 → Vec 1} {alpha Ka KF Lam : ℝ}
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
    ∃ c : ℝ, ∃ G : Vec 1 → Vec 1,
      (∀ x, G x 0 = (c - F x 0) / a x 0 0) ∧
      G =ᵐ[volumeOn (euclideanBall (0 : Vec 1) 1)] u.grad ∧
      ContinuousOn G (euclideanBall (0 : Vec 1) 1) ∧
      ∀ x ∈ euclideanBall (0 : Vec 1) 1,
        a x 0 0 * G x 0 + F x 0 = c := by
  let B := euclideanBall (0 : Vec 1) 1
  have hBmeas : MeasurableSet B := (isOpen_euclideanBall _ _).measurableSet
  have hBtop : volume B < ∞ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top (0 : Vec 1) (by norm_num))
  let : IsFiniteMeasure (volumeOn B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBtop⟩
  have hzero : (0 : Vec 1) ∈ B := center_mem_euclideanBall _ (by norm_num)
  have haCont : ContinuousOn (fun x => a x 0 0) B :=
    (ha.coordinate 0 0).continuousOn halpha hKa
  have hFCont : ContinuousOn (fun x => F x 0) B :=
    (hF.coordinate 0).continuousOn halpha hKF
  have hu1 : Integrable (fun x => u.grad x 0) (volumeOn B) :=
    memLp_one_iff_integrable.mp ((u.gradMemL2 0).mono_exponent (by norm_num))
  have haflux : Integrable (fun x => a x 0 0 * u.grad x 0) (volumeOn B) := by
    apply Integrable.mono' (hu1.norm.const_mul Lam)
    · exact (haCont.aestronglyMeasurable hBmeas).mul (u.gradMemL2 0).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hBmeas] with x hx
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_apply_le_of_isEllipticMatrix (hell x hx) 0 0) (abs_nonneg _)
  have hFint : Integrable (fun x => F x 0) (volumeOn B) := by
    let C := |F 0 0| + KF
    apply Integrable.mono' (integrable_const C)
    · exact hFCont.aestronglyMeasurable hBmeas
    · filter_upwards [ae_restrict_mem hBmeas] with x hx
      have hd := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
      have hh := (hF.coordinate 0) x hx 0 hzero
      have hp : vecEuclideanNorm (x - 0) ^ alpha ≤ 1 :=
        Real.rpow_le_one (vecEuclideanNorm_nonneg _) hd.le halpha.le
      have hdiff : |F x 0 - F 0 0| ≤ KF :=
        hh.trans (by simpa using mul_le_mul_of_nonneg_left hp hKF)
      rw [Real.norm_eq_abs]
      calc
        |F x 0| = |(F x 0 - F 0 0) + F 0 0| := by ring_nf
        _ ≤ |F x 0 - F 0 0| + |F 0 0| := abs_add_le _ _
        _ ≤ C := by dsimp [C]; linarith
  have hflux : IntegrableOn
      (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0) B := by
    change Integrable (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0)
      (volumeOn B)
    simpa [matVecMul] using! haflux.add hFint
  let c := integralAverage B
    (fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0)
  have hfluxAE := oneDimensional_totalFlux_ae_eq_integralAverage
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 1) (by norm_num))
    (volume_euclideanBall_pos (0 : Vec 1) (by norm_num)) hBtop hsol hflux
  let G : Vec 1 → Vec 1 := fun x _ => (c - F x 0) / a x 0 0
  have hGa : G =ᵐ[volumeOn B] u.grad := by
    filter_upwards [hfluxAE, ae_restrict_mem hBmeas] with x hfx hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have ha1 := oneDimensional_diag_lower (hell x hx)
    have hm : (matVecMul (a x) (u.grad x)) 0 = a x 0 0 * u.grad x 0 := by
      simp [matVecMul]
    dsimp only [G, c]
    rw [hm] at hfx
    apply (div_eq_iff (ne_of_gt (lt_of_lt_of_le zero_lt_one ha1))).2
    linarith
  have hGCont : ContinuousOn G B := by
    apply continuousOn_pi.mpr
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (continuousOn_const.sub hFCont).div haCont fun x hx =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one (oneDimensional_diag_lower (hell x hx)))
  refine ⟨c, G, fun x => rfl, ?_, hGCont, ?_⟩
  · simpa only [B] using hGa
  · intro x hx
    have ha1 := oneDimensional_diag_lower (hell x hx)
    dsimp only [G]
    rw [mul_div_cancel₀ (c - F x 0)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ha1))]
    ring

end

end PDE
