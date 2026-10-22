module

public import PDEFoundation.Analysis.SmoothCompactCoordinateIBP
public import PDEFoundation.Measure.EuclideanFieldMeanLp
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare

/-! # Smooth zero-boundary Poincaré inequality -/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

private instance instNontrivialVecSZBP (d : ℕ) [NeZero d] : Nontrivial (Vec d) := inferInstance
private instance instNoncompactSpaceVecSZBP (d : ℕ) [NeZero d] : NoncompactSpace (Vec d) := inferInstance

private theorem setIntegral_eq_neg_setIntegral_fderiv_mul_centered_coord
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ U) (i : Fin d) (z : Vec d) :
    ∫ x in U, f x ∂volume =
      -∫ x in U, (fderiv ℝ f x) (basisVec i) * (x i - z i) ∂volume := by
  have hzero_f : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    exact image_eq_zero_of_notMem_tsupport (fun hxt => hxU (hf_sub hxt))
  have hzero_d : ∀ x, x ∉ U →
      (fderiv ℝ f x) (basisVec i) * (x i - z i) = 0 := by
    intro x hxU
    have hnot : x ∉ tsupport f := fun hxt => hxU (hf_sub hxt)
    have hd : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
    simp [hd]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_f,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero_d,
    integral_eq_neg_integral_fderiv_mul_centered_coord hf hf_supp i z]

private theorem abs_integral_le_diameter_mul_integral_grad
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {D : ℝ}
    (hUmeas : MeasurableSet U) (hdiam : HasEuclideanDiameterLE U D)
    {z : Vec d} (hz : z ∈ U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ U) :
    |∫ x in U, f x ∂volume| ≤
      D * ∫ x in U, vecEuclideanNorm (classicalGradient f x) ∂volume := by
  let i : Fin d := 0
  have hgradCont : Continuous (fun x => vecEuclideanNorm (classicalGradient f x)) :=
    continuous_vecEuclideanNorm.comp
      (PDE.ContDiff.continuous_classicalGradient (hf.of_le (by simp)))
  have hgradSupp : HasCompactSupport (fun x => vecEuclideanNorm (classicalGradient f x)) := by
    refine (hf_supp.fderiv (𝕜 := ℝ)).mono ?_
    intro x hx
    change vecEuclideanNorm (classicalGradient f x) ≠ 0 at hx
    change fderiv ℝ f x ≠ 0
    intro hzero
    apply hx
    change vecEuclideanNorm (fun j => (fderiv ℝ f x) (basisVec j)) = 0
    rw [hzero]
    apply vecEuclideanNorm_eq_zero_iff.mpr
    funext j
    simp
  have hgradInt : IntegrableOn (fun x => vecEuclideanNorm (classicalGradient f x)) U volume :=
    (hgradCont.integrable_of_hasCompactSupport hgradSupp).restrict
  have htermInt : IntegrableOn
      (fun x => (fderiv ℝ f x) (basisVec i) * (x i - z i)) U volume := by
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
    have hdcont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) :=
      (hf1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport
        (fun x => (fderiv ℝ f x) (basisVec i) * (x i - z i)) :=
      (hf_supp.fderiv_apply ℝ _).mul_right
    exact (hdcont.mul (by fun_prop)).integrable_of_hasCompactSupport hsupp |>.restrict
  rw [setIntegral_eq_neg_setIntegral_fderiv_mul_centered_coord
    hf hf_supp hf_sub i z, abs_neg]
  calc
    |∫ x in U, (fderiv ℝ f x) (basisVec i) * (x i - z i) ∂volume|
        ≤ ∫ x in U, |(fderiv ℝ f x) (basisVec i) * (x i - z i)| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in U, D * vecEuclideanNorm (classicalGradient f x) ∂volume := by
      apply integral_mono_ae htermInt.norm (hgradInt.const_mul D)
      filter_upwards [ae_restrict_mem hUmeas] with x hx
      simp only [Real.norm_eq_abs, abs_mul]
      have hc := abs_apply_le_vecEuclideanNorm (x - z) i
      have hd := hdiam hx hz
      have hg := abs_apply_le_vecEuclideanNorm (classicalGradient f x) i
      calc
        |(fderiv ℝ f x) (basisVec i)| * |x i - z i|
            ≤ vecEuclideanNorm (classicalGradient f x) * D := by
          exact mul_le_mul (by simpa [classicalGradient] using hg)
            (by simpa [Pi.sub_apply] using hc.trans hd) (abs_nonneg _)
            (vecEuclideanNorm_nonneg _)
        _ = D * vecEuclideanNorm (classicalGradient f x) := mul_comm _ _
    _ = D * ∫ x in U, vecEuclideanNorm (classicalGradient f x) ∂volume :=
      by rw [integral_const_mul]

private theorem abs_integralAverage_le_diameter_mul_eLpMeanNorm_grad
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hq : 1 < q)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (φ : WeakTestFunction U) :
    ENNReal.ofReal |integralAverage U φ.toFun| ≤
      ENNReal.ofReal D *
        euclideanFieldELpMeanNormOn U (ENNReal.ofReal q)
          (classicalGradient φ.toFun) := by
  let p : ENNReal := ENNReal.ofReal q
  let G : Vec d → ℝ := fun x => vecEuclideanNorm (classicalGradient φ.toFun x)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hp1 : (1 : ENNReal) ≤ p := by
    dsimp [p]
    exact ENNReal.one_le_ofReal.mpr hq.le
  let u : W1pFunction U p :=
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
      (φ.contDiff.of_le (by simp))
  have hGraw : MemLp G p (volumeOn U) := by
    have hHilbert : MemLp (toHilbertVecField (classicalGradient φ.toFun)) p
        (volumeOn U) := by
      apply gradMemLpOn_iff_memLp_toHilbertVecField.mp
      simpa only [u, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_grad]
        using u.gradMemLp
    exact MemLp.ae_eq
      (Filter.Eventually.of_forall fun x =>
        norm_toHilbertVecField_apply (classicalGradient φ.toFun) x)
      hHilbert.norm
  have hGmean : MemLp G p (normalizedVolumeOn U) :=
    memLp_normalizedVolumeOn_of_memLpOn hGraw hUPos
  let : IsProbabilityMeasure (normalizedVolumeOn U) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUPos hUTop
  have hGone : MemLp G 1 (normalizedVolumeOn U) := hGmean.mono_exponent hp1
  have hL1 :
      ENNReal.ofReal (∫ x, G x ∂normalizedVolumeOn U) =
        eLpNorm G 1 (normalizedVolumeOn U) := by
    rw [hGone.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs]
    rw [show (fun x => G x) = fun x => |G x| by
      funext x
      exact (abs_of_nonneg (vecEuclideanNorm_nonneg _)).symm]
  have hUne : U.Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero hUPos.ne'
  obtain ⟨z, hz⟩ := hUne
  have hMeanRaw := abs_integral_le_diameter_mul_integral_grad
    hU.measurableSet hdiam hz φ.contDiff φ.hasCompactSupport
    φ.tsupport_subset
  have hMean : |integralAverage U φ.toFun| ≤
      D * ∫ x, G x ∂normalizedVolumeOn U := by
    rw [← integral_normalizedVolumeOn_eq_integralAverage]
    rw [normalizedVolumeOn, integral_smul_measure, ENNReal.toReal_inv]
    rw [integral_smul_measure, ENNReal.toReal_inv]
    simp only [smul_eq_mul]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (volume U).toReal⁻¹)]
    calc
      (volume U).toReal⁻¹ * |∫ x in U, φ.toFun x ∂volume|
          ≤ (volume U).toReal⁻¹ *
              (D * ∫ x in U, G x ∂volume) :=
        mul_le_mul_of_nonneg_left hMeanRaw (by positivity)
      _ = D * ((volume U).toReal⁻¹ * ∫ x in U, G x ∂volume) := by ring
  have hen := ENNReal.ofReal_le_ofReal hMean
  rw [ENNReal.ofReal_mul (hdiam.nonneg ⟨z, hz⟩), hL1] at hen
  exact hen.trans
    (mul_le_mul_right (eLpNorm_le_eLpNorm_of_exponent_le hp1) _)

/-- A smooth compactly supported test function satisfies the unnormalized
zero-boundary Poincaré inequality on a bounded open convex domain. -/
theorem eLpNormOn_testFunction_le_two_pow_add_one_mul_diameter_grad
    {d : ℕ} (hd : 0 < d) {U : Set (Vec d)} {D q : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hdiam : HasEuclideanDiameterLE U D) (hD : 0 ≤ D)
    (hq : 1 < q) (φ : WeakTestFunction U) :
    eLpNormOn U (ENNReal.ofReal q) φ.toFun ≤
      ENNReal.ofReal (((2 : ℝ) ^ d + 1) * D) *
        euclideanFieldELpNormOn U (ENNReal.ofReal q)
          (classicalGradient φ.toFun) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  by_cases hUne : U.Nonempty
  · have hUPos : 0 < volume U := hU.isOpen.measure_pos volume hUne
    have hUTop : volume U < ∞ :=
      hU.isSobolevRegularDomain.volume_lt_top
    let p : ENNReal := ENNReal.ofReal q
    let u : W1pFunction U p :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
        (φ.contDiff.of_le (by simp))
    have hφraw : MemLp φ.toFun p (volumeOn U) := by
      simpa only [u, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_toFun]
        using u.memLp
    have hφmean := memLp_normalizedVolumeOn_of_memLpOn hφraw hUPos
    have : IsProbabilityMeasure (normalizedVolumeOn U) :=
      isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hUPos hUTop
    have hconst : MemLp (fun _ : Vec d => integralAverage U φ.toFun) p
        (normalizedVolumeOn U) := memLp_const _
    have hsub := hφmean.sub hconst
    have hp1 : (1 : ENNReal) ≤ p := by
      dsimp [p]
      exact ENNReal.one_le_ofReal.mpr hq.le
    have htri : eLpMeanNormOn U p φ.toFun ≤
        eLpMeanNormOn U p (fun x => φ.toFun x - integralAverage U φ.toFun) +
          eLpMeanNormOn U p (fun _ : Vec d => integralAverage U φ.toFun) := by
      calc
        eLpMeanNormOn U p φ.toFun =
            eLpNorm ((fun x => φ.toFun x - integralAverage U φ.toFun) +
              fun _ => integralAverage U φ.toFun) p (normalizedVolumeOn U) := by
          apply eLpNorm_congr_ae
          filter_upwards with x
          simp
        _ ≤ _ := eLpNorm_add_le
          hp1
    have hcenter := eLpMeanNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
      hU hdiam hD φ.contDiff hq.le hUPos hUTop
    have hmean := abs_integralAverage_le_diameter_mul_eLpMeanNorm_grad
      hU hdiam hq hUPos hUTop φ
    have hconstEq : eLpMeanNormOn U p
        (fun _ : Vec d => integralAverage U φ.toFun) =
      ENNReal.ofReal |integralAverage U φ.toFun| := by
      rw [eLpMeanNormOn, eLpNorm_const' _]
      · rw [Real.enorm_eq_ofReal_abs]
        simp
      · intro hp0
        exact (not_le_of_gt (zero_lt_one.trans hq))
          (ENNReal.ofReal_eq_zero.mp hp0)
      · exact ENNReal.ofReal_ne_top
    have hnormalized : eLpMeanNormOn U p φ.toFun ≤
        ENNReal.ofReal (((2 : ℝ) ^ d + 1) * D) *
          euclideanFieldELpMeanNormOn U p (classicalGradient φ.toFun) := by
      rw [hconstEq] at htri
      calc
        eLpMeanNormOn U p φ.toFun ≤ _ := htri
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ d * D) *
              euclideanFieldELpMeanNormOn U p (classicalGradient φ.toFun) +
            ENNReal.ofReal D *
              euclideanFieldELpMeanNormOn U p (classicalGradient φ.toFun) :=
          add_le_add hcenter hmean
        _ = ENNReal.ofReal (((2 : ℝ) ^ d + 1) * D) *
              euclideanFieldELpMeanNormOn U p (classicalGradient φ.toFun) := by
          rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (by positivity) hD) hD]
          congr 2
          ring
    rw [eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hUPos hUTop,
      euclideanFieldELpNormOn_eq_volume_rpow_mul hUPos hUTop]
    calc
      volume U ^ (1 / p).toReal * eLpMeanNormOn U p φ.toFun ≤
          volume U ^ (1 / p).toReal *
            (ENNReal.ofReal (((2 : ℝ) ^ d + 1) * D) *
              euclideanFieldELpMeanNormOn U p (classicalGradient φ.toFun)) :=
        mul_le_mul_right hnormalized _
      _ = ENNReal.ofReal (((2 : ℝ) ^ d + 1) * D) *
          (volume U ^ (1 / p).toReal *
            euclideanFieldELpMeanNormOn U p (classicalGradient φ.toFun)) := by
        ac_rfl
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hUne
    subst U
    simp [eLpNormOn, euclideanFieldELpNormOn]

end

end PDE
