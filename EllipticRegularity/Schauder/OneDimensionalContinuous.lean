module

public import EllipticRegularity.Schauder.OneDimensionalEllipticFlux

/-! # One-dimensional Schauder estimate for elliptic coefficients

The one-dimensional weak equation has constant total flux. Uniform ellipticity
then gives a Hölder representative without any coefficient modulus in the
constant.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The native one-dimensional weak equation, with a general uniformly
elliptic coefficient, yields a Hölder representative on the half ball. -/
theorem hasEuclideanHolderRepresentativeOn_halfBall_oneDimensional_of_elliptic_weakSolution
    {a : CoeffField 1} {α p Lam : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 < p) (hpα : 1 - 1 / p = α)
    (u : H1Function (euclideanBall (0 : Vec 1) 1)) {F : Vec 1 → Vec 1}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 1) 1, IsEllipticMatrix 1 Lam (a x))
    (hF : MemLpOn (euclideanBall (0 : Vec 1) 1) (ENNReal.ofReal p)
      (fun x => F x 0))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec 1) 1) u 0 F) :
    HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec 1) (1 / 2))
      u.toFun α
      (8 * (1 + Lam) *
        ((eLpNorm (fun x => u.grad x 0) 2
          (volumeOn (euclideanBall (0 : Vec 1) 1))).toReal +
        (eLpNorm (fun x => F x 0) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec 1) 1))).toReal)) := by
  have hball := euclideanBall_zero_one_eq_axisBox (by norm_num : (0 : ℝ) < 1)
  let us := scalarPullbackOne u.toFun
  let gs := scalarPullbackOne (fun x => u.grad x 0)
  let Fs := scalarPullbackOne (fun x => F x 0)
  let ks := scalarPullbackOne (fun x => a x 0 0)
  let q : Vec 1 → ℝ := fun x => (matVecMul (a x) (u.grad x)) 0 + F x 0
  have huScalar : MemLp us 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply (memLp_liftOneDimensional_iff_memLp_Ioo (-1) 1).mp
    rw [liftOneDimensional_scalarPullbackOne, ← hball]
    exact u.memL2
  have hgScalar : MemLp gs 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply (memLp_liftOneDimensional_iff_memLp_Ioo (-1) 1).mp
    rw [liftOneDimensional_scalarPullbackOne, ← hball]
    exact u.gradMemL2 0
  have hFScalar : MemLp Fs (ENNReal.ofReal p)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply (memLp_liftOneDimensional_iff_memLp_Ioo (-1) 1).mp
    rw [liftOneDimensional_scalarPullbackOne, ← hball]
    exact hF
  have hweak : HasWeakDerivOnIoo (-1) 1 us gs := by
    unfold HasWeakDerivOnIoo
    rw [liftOneDimensional_scalarPullbackOne, liftOneDimensional_scalarPullbackOne,
      ← hball]
    exact u.hasWeakPartialDerivOn 0
  let : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec 1) 1)) :=
    isFiniteMeasure_volumeOn_euclideanBall _ (by norm_num)
  have hgradInt : IntegrableOn (fun x => u.grad x 0)
      (euclideanBall (0 : Vec 1) 1) :=
    (u.gradMemL2 0).integrable (by norm_num)
  have hflux : IntegrableOn (fun x => a x 0 0 * u.grad x 0)
      (euclideanBall (0 : Vec 1) 1) := by
    apply Integrable.mono' (hgradInt.norm.const_mul Lam)
    · exact (ha 0 0).aestronglyMeasurable.mul (u.gradMemL2 0).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_euclideanBall _ _)] with x hx
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_apply_le_of_isEllipticMatrix (hell x hx) 0 0) (abs_nonneg _)
  have hFInt : IntegrableOn (fun x => F x 0) (euclideanBall (0 : Vec 1) 1) :=
    hF.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hq : IntegrableOn q (euclideanBall (0 : Vec 1) 1) := by
    dsimp only [q]
    simpa only [matVecMul, Fin.sum_univ_one] using! hflux.add hFInt
  have hcNative := oneDimensional_totalFlux_ae_eq_integralAverage
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 1) (by norm_num))
    (volume_euclideanBall_pos _ (by norm_num))
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))) hsol hq
  let c := integralAverage (euclideanBall (0 : Vec 1) 1) q
  have hqScalar : IntegrableOn (fun t => ks t * gs t + Fs t)
      (Ioo (-1 : ℝ) 1) := by
    apply (integrableOn_axisBox_one_iff_integrableOn_Ioo (-1) 1).mp
    rw [← hball]
    convert hq using 1
    funext x
    simp only [q, ks, gs, Fs, scalarPullbackOne, liftOneDimensional,
      scalarToVecOne_vecOneCoordinate, matVecMul, Fin.sum_univ_one]
  have hcScalar : (fun t => ks t * gs t + Fs t) =ᵐ[
      volume.restrict (Ioo (-1 : ℝ) 1)] fun _ => c := by
    have hnative : ∀ᵐ x ∂volume.restrict (oneDimensionalAxisBox (-1) 1),
        q x = c := by simpa only [← hball] using! hcNative
    have h := (ae_scalarToVecOne_iff (a := -1) (b := 1)
      (P := fun x => q x = c)).mpr hnative
    simpa only [q, ks, gs, Fs, scalarPullbackOne, matVecMul,
      Fin.sum_univ_one] using! h
  have hLam : 1 ≤ Lam :=
    (hell 0 (center_mem_euclideanBall _ (by norm_num))).lam_le_Lam
  have hkNative : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 1) 1),
      1 ≤ a x 0 0 ∧ a x 0 0 ≤ Lam := by
    filter_upwards [ae_restrict_mem (measurableSet_euclideanBall _ _)] with x hx
    have hA := hell x hx
    constructor
    · have h := hA.coercive (basisVec 0)
      norm_num [vecNormSq, vecDot, matVecMul, basisVec] at h ⊢
      exact h
    · exact (abs_le.mp (abs_apply_le_of_isEllipticMatrix hA 0 0)).2
  have hkScalar : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1),
      1 ≤ ks t ∧ ks t ≤ Lam := by
    have hnative : ∀ᵐ x ∂volume.restrict (oneDimensionalAxisBox (-1) 1),
        1 ≤ a x 0 0 ∧ a x 0 0 ≤ Lam := by simpa only [← hball] using hkNative
    exact (ae_scalarToVecOne_iff (a := -1) (b := 1)).mpr hnative
  obtain ⟨v, huv, hv⟩ :=
    exists_holder_representative_of_unitInterval_elliptic_constantFlux
      hα hα1 hp hpα hLam huScalar hgScalar hweak hFScalar hqScalar hkScalar hcScalar
  have hnormg : eLpNorm gs 2 (volume.restrict (Ioo (-1 : ℝ) 1)) =
      eLpNorm (fun x => u.grad x 0) 2
        (volumeOn (euclideanBall (0 : Vec 1) 1)) := by
    rw [← eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo (-1) 1,
      liftOneDimensional_scalarPullbackOne, ← hball]
  have hnormF : eLpNorm Fs (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)) =
      eLpNorm (fun x => F x 0) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec 1) 1)) := by
    rw [← eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo (-1) 1,
      liftOneDimensional_scalarPullbackOne, ← hball]
  have hAE : liftOneDimensional v =ᵐ[volumeOn (euclideanBall (0 : Vec 1) 1)]
      u.toFun := by
    have h := (aeEq_liftOneDimensional_iff_aeEq_Ioo (-1) 1).mpr huv.symm
    simpa only [us, liftOneDimensional_scalarPullbackOne, volumeOn, ← hball] using h
  refine ⟨liftOneDimensional v,
    ae_restrict_of_ae_restrict_of_subset
      (euclideanBall_mono (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hAE, ?_⟩
  intro x hx y hy
  have hhalf := euclideanBall_zero_one_eq_axisBox (by norm_num : (0 : ℝ) < 1 / 2)
  rw [hhalf, mem_oneDimensionalAxisBox_iff] at hx hy
  simp only [neg_div] at hv
  have h := hv (vecOneCoordinate x) hx (vecOneCoordinate y) hy
  rw [hnormg, hnormF] at h
  simpa only [liftOneDimensional, vecEuclideanNorm_one_eq_abs, Pi.sub_apply,
    vecOneCoordinate] using h

/-- The source-shaped one-dimensional continuous-coefficient Schauder
corollary. The constant depends only on the upper ellipticity parameter. -/
theorem schauder_oneDimensional_continuous
    {a : CoeffField 1} {α Lam : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (u : H1Function (euclideanBall (0 : Vec 1) 1)) {F : Vec 1 → Vec 1}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec 1) 1, IsEllipticMatrix 1 Lam (a x))
    (hFmeas : AEStronglyMeasurable (fun x => F x 0)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hF : MemLpOn (euclideanBall (0 : Vec 1) 1)
      (ENNReal.ofReal (1 / (1 - α))) (fun x => vecEuclideanNorm (F x)))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec 1) 1) u 0 F) :
    HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec 1) (1 / 2))
      u.toFun α
      ((32 * (1 + |Lam|) / α) *
        (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1,
          vecNormSq (u.grad x)) +
        (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
          (ENNReal.ofReal (1 / (1 - α))) F).toReal / (1 - α))) := by
  have hp : 1 < 1 / (1 - α) := by
    rw [lt_div_iff₀ (sub_pos.mpr hα1)]
    linarith
  have hpα : 1 - 1 / (1 / (1 - α)) = α := by
    field_simp
    ring
  have hFcoord : MemLpOn (euclideanBall (0 : Vec 1) 1)
      (ENNReal.ofReal (1 / (1 - α))) (fun x => F x 0) := by
    apply hF.of_le hFmeas
    filter_upwards with x
    simp only [Real.norm_eq_abs, vecEuclideanNorm_one_eq_abs, abs_abs]
    exact le_rfl
  obtain ⟨v, hvAE, hv⟩ :=
    hasEuclideanHolderRepresentativeOn_halfBall_oneDimensional_of_elliptic_weakSolution
      hα hα1 hp hpα u ha hell hFcoord hsol
  have hnormF : eLpNorm (fun x => F x 0) (ENNReal.ofReal (1 / (1 - α)))
      (volumeOn (euclideanBall (0 : Vec 1) 1)) =
      euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal (1 / (1 - α))) F := by
    unfold euclideanFieldELpNormOn eLpNormOn
    simp only [vecEuclideanNorm_one_eq_abs, ← Real.norm_eq_abs]
    exact (eLpNorm_norm (fun x => F x 0) hFmeas).symm
  rw [eLpNorm_coord_one_two_toReal_eq_sqrt_energy u.gradMemL2, hnormF] at hv
  refine ⟨v, hvAE, hv.mono_const ?_⟩
  have hLam : 1 ≤ Lam :=
    (hell 0 (center_mem_euclideanBall _ (by norm_num))).lam_le_Lam
  have hgap : 0 < 1 - α := sub_pos.mpr hα1
  have hG : 0 ≤ Real.sqrt
      (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) :=
    Real.sqrt_nonneg _
  have hFnorm : 0 ≤ (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
      (ENNReal.ofReal (1 / (1 - α))) F).toReal := ENNReal.toReal_nonneg
  have hLamAbs : Lam ≤ |Lam| := le_abs_self Lam
  have hαle : α ≤ 1 := hα1.le
  have hgaple : 1 - α ≤ 1 := by linarith
  have hcoeff : 8 * (1 + Lam) ≤ 32 * (1 + |Lam|) / α := by
    apply (le_div_iff₀ hα).2
    have hmul : α * (1 + Lam) ≤ 1 + Lam :=
      mul_le_of_le_one_left (by linarith : 0 ≤ 1 + Lam) hαle
    nlinarith [abs_nonneg Lam]
  have hforcingScale :
      (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal (1 / (1 - α))) F).toReal ≤
      (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal (1 / (1 - α))) F).toReal / (1 - α) := by
    apply (le_div_iff₀ hgap).2
    simpa only [mul_comm] using mul_le_of_le_one_right hFnorm hgaple
  have hsum : Real.sqrt
        (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) +
      (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal (1 / (1 - α))) F).toReal ≤
      Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) +
      (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal (1 / (1 - α))) F).toReal / (1 - α) :=
    add_le_add le_rfl hforcingScale
  calc
    _ ≤ (32 * (1 + |Lam|) / α) *
        (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) +
          (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
            (ENNReal.ofReal (1 / (1 - α))) F).toReal) :=
      mul_le_mul_of_nonneg_right hcoeff (add_nonneg hG hFnorm)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
      (div_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one (abs_nonneg Lam))) hα.le)

end

end PDE
