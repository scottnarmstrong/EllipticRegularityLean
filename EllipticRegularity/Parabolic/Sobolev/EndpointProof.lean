/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
-/
module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceSmooth
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic

open MeasureTheory

private theorem holderTriple_two_two_one : Real.HolderTriple 2 2 1 := by
  exact ⟨by norm_num [one_div], by norm_num, by norm_num⟩

private theorem eLpNorm_double_mul_le
    {f g : Vec 2 → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => (2 : ℝ) * f x * g x) 1 volume ≤
      ENNReal.ofReal 2 * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  let : (ENNReal.ofReal 2).HolderTriple (ENNReal.ofReal 2) 1 := by
    simpa only [ENNReal.ofReal_one] using
      holderTriple_two_two_one.ennrealOfReal
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (fun a b : ℝ => (2 : ℝ) * a * b) 2
    (by fun_prop) hf hg
    (p := ENNReal.ofReal 2) (q := ENNReal.ofReal 2) (r := 1)
    (Filter.Eventually.of_forall fun x => by
      change |(2 : ℝ) * f x * g x| ≤ (2 : ℝ) * |f x| * |g x|
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      )
  simpa using h

private theorem scalar_compact_linf_sq
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (x : ℝ) :
    |f x| ^ 2 ≤
      2 * (∫ t, |f t| ^ 2 ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) *
        (∫ t, |deriv f t| ^ 2 ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
  let y : ℝ := min (Classical.choose hc.isCompact.bddBelow) x - 1
  have hyx : y < x := by
    dsimp [y]
    linarith [min_le_right (Classical.choose hc.isCompact.bddBelow) x]
  have hya : y < Classical.choose hc.isCompact.bddBelow := by
    dsimp [y]
    linarith [min_le_left (Classical.choose hc.isCompact.bddBelow) x]
  have hyts : y ∉ tsupport f := by
    intro hy
    have hle := Classical.choose_spec hc.isCompact.bddBelow hy
    linarith
  have hfy : f y = 0 := by
    by_contra hne
    exact hyts (subset_tsupport f (by simpa [Function.mem_support] using hne))
  let F : ℝ → ℝ := fun t => f t * f t
  have hF : ContDiff ℝ 1 F := by
    exact (hf.mul hf).of_le (by norm_num)
  have hFTC : (∫ t in y..x, deriv F t) = F x - F y :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hF.contDiffOn hyx.le
  have hderiv (t : ℝ) : deriv F t = 2 * f t * deriv f t := by
    change deriv (f * f) t = _
    rw [deriv_mul (hf.differentiable (by simp) t)
      (hf.differentiable (by simp) t)]
    ring
  have hmemF : MemLp f 2 (volume : Measure ℝ) :=
    hf.continuous.memLp_of_hasCompactSupport hc
  have hcderiv : HasCompactSupport (deriv f) := by
    have hEq : (fun t => deriv f t) = fun t => (fderiv ℝ f t) 1 := by
      funext t
      exact (hf.differentiable (by norm_num) t).hasDerivAt.deriv
    simpa only [hEq] using hc.fderiv_apply (𝕜 := ℝ) (1 : ℝ)
  have hmemD : MemLp (deriv f) 2 (volume : Measure ℝ) := by
    exact (hf.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hcderiv
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    (μ := (volume : Measure ℝ))
    Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hmemF)
    (by simpa only [ENNReal.ofReal_ofNat] using hmemD)
  have hprodInt : Integrable (fun t => 2 * |f t| * |deriv f t|)
      (volume : Measure ℝ) := by
    simpa [Real.norm_eq_abs, norm_mul, mul_assoc] using
      (hmemF.integrable_mul hmemD).norm.const_mul 2
  have hderivFInt : Integrable (deriv F) (volume : Measure ℝ) := by
    have hcF : HasCompactSupport F := hc.mul_right
    have hEq : (fun t => deriv F t) = fun t => (fderiv ℝ F t) 1 := by
      funext t
      exact (hF.differentiable (by norm_num) t).hasDerivAt.deriv
    have hcont : Continuous (fun t => (fderiv ℝ F t) 1) :=
      (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hint : Integrable (fun t => (fderiv ℝ F t) 1) volume :=
      hcont.integrable_of_hasCompactSupport (hcF.fderiv_apply (𝕜 := ℝ) (1 : ℝ))
    simpa only [hEq] using hint
  have hIntBound :
      (∫ t in Set.Ioc y x, |deriv F t|) ≤
        2 * (∫ t, |f t| * |deriv f t| ∂(volume : Measure ℝ)) := by
    calc
      _ ≤ ∫ t in Set.Ioc y x, 2 * |f t| * |deriv f t| := by
        apply integral_mono_ae (hderivFInt.norm.restrict)
          (hprodInt.restrict)
        filter_upwards with t
        rw [Real.norm_eq_abs, hderiv t]
        norm_num [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
          mul_assoc]
      _ ≤ ∫ t, 2 * |f t| * |deriv f t| :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun t => by positivity) hprodInt
      _ = ∫ t, 2 * (|f t| * |deriv f t|) := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = 2 * ∫ t, |f t| * |deriv f t| := by rw [integral_const_mul]
  have hFTC' : (∫ t in y..x, deriv F t) = f x * f x := by
    rw [hFTC]
    simp [F, hfy]
  calc
    |f x| ^ 2 = ‖∫ t in y..x, deriv F t‖ := by
      rw [hFTC']
      simp [Real.norm_eq_abs, sq_abs]
      ring
    _ ≤ ∫ t in Set.Ioc y x, |deriv F t| := by
      simpa only [Real.norm_eq_abs, intervalIntegral.integral_of_le hyx.le] using
        intervalIntegral.norm_integral_le_integral_norm
          (f := fun t => deriv F t) (μ := volume) hyx.le
    _ ≤ 2 * (∫ t, |f t| * |deriv f t| ∂(volume : Measure ℝ)) := hIntBound
    _ ≤ _ := by
      have h := hHolder
      have h' :
          2 * ∫ t, |f t| * |deriv f t| ∂(volume : Measure ℝ) ≤
            2 * ((∫ t, |f t| ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) *
              (∫ t, |deriv f t| ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ)) := by
        simpa only [Real.norm_eq_abs, mul_assoc] using
          (mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (2 : ℝ)))
      have hpF :
          (∫ t, |f t| ^ (2 : ℝ) ∂(volume : Measure ℝ)) =
            ∫ t, |f t| ^ 2 ∂(volume : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards with t
        exact Real.rpow_natCast _ 2
      have hpD :
          (∫ t, |deriv f t| ^ (2 : ℝ) ∂(volume : Measure ℝ)) =
            ∫ t, |deriv f t| ^ 2 ∂(volume : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards with t
        exact Real.rpow_natCast _ 2
      rw [hpF, hpD] at h'
      simpa [mul_assoc] using h'

private theorem smooth_scalar_one_dimensional_gagliardo_nirenberg
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    (∫ t, |f t| ^ 6 ∂(volume : Measure ℝ)) ≤
      4 * (∫ t, |f t| ^ 2 ∂(volume : Measure ℝ)) ^ 2 *
        (∫ t, |deriv f t| ^ 2 ∂(volume : Measure ℝ)) := by
  let A : ℝ := ∫ t, |f t| ^ 2 ∂(volume : Measure ℝ)
  let B : ℝ := ∫ t, |deriv f t| ^ 2 ∂(volume : Measure ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun t => sq_nonneg |f t|
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun t => sq_nonneg |deriv f t|
  have hAbsCompact : HasCompactSupport (fun t => |f t|) :=
    HasCompactSupport.abs hc
  have hPowCompact : ∀ n : ℕ, HasCompactSupport (fun t => |f t| ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hAbsCompact
    | succ n ih =>
        have h := ih.mul_right (f' := fun t => |f t|)
        convert h using 1
        funext t
        simp only [Pi.mul_apply, pow_succ]
  have hSqCompact : HasCompactSupport (fun t => |f t| ^ 2) := by
    simpa using hPowCompact 1
  have hSixCompact : HasCompactSupport (fun t => |f t| ^ 6) := by
    simpa using hPowCompact 5
  have hSq : Integrable (fun t => |f t| ^ 2) (volume : Measure ℝ) := by
    exact (hf.continuous.abs.pow 2).integrable_of_hasCompactSupport hSqCompact
  have hSix : Integrable (fun t => |f t| ^ 6) (volume : Measure ℝ) := by
    exact (hf.continuous.abs.pow 6).integrable_of_hasCompactSupport hSixCompact
  have hpoint : ∀ t : ℝ, |f t| ^ 6 ≤ (4 * A * B) * |f t| ^ 2 := by
    intro t
    have hsup := scalar_compact_linf_sq hf hc t
    have hsup' : |f t| ^ 2 ≤ 2 * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
      simpa only [A, B] using hsup
    have hfour : |f t| ^ 4 ≤ 4 * A * B := by
      calc
        |f t| ^ 4 = (|f t| ^ 2) ^ 2 := by ring
        _ ≤ (2 * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
        _ = 4 * A * B := by
          rw [← Real.sqrt_eq_rpow A, ← Real.sqrt_eq_rpow B]
          calc
            _ = 4 * (Real.sqrt A) ^ 2 * (Real.sqrt B) ^ 2 := by ring
            _ = 4 * A * B := by rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
    calc
      |f t| ^ 6 = |f t| ^ 4 * |f t| ^ 2 := by ring
      _ ≤ (4 * A * B) * |f t| ^ 2 := by gcongr
  calc
    _ ≤ ∫ t, (4 * A * B) * |f t| ^ 2 ∂(volume : Measure ℝ) :=
      integral_mono_ae hSix (hSq.const_mul (4 * A * B))
        (Filter.Eventually.of_forall hpoint)
    _ = 4 * A * B * A := by rw [integral_const_mul]
    _ = 4 * A ^ 2 * B := by dsimp [A]; ring

private theorem scalarVecEuclideanNorm_fin_one (v : Vec 1) :
    vecEuclideanNorm v = |v 0| := by
  unfold vecEuclideanNorm vecNormSq vecDot
  simp only [Fin.sum_univ_one]
  rw [← pow_two, Real.sqrt_sq_eq_abs]

private theorem scalarPullbackOne_hasCompactSupport
    {f : Vec 1 → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (scalarPullbackOne f) := by
  let e := scalarToVecOneContinuousLinearEquiv
  have hK : IsCompact (e.symm '' tsupport f) := hc.isCompact.image e.symm.continuous
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro t ht
  have hne : f (e t) ≠ 0 := by
    simpa [Function.mem_support, scalarPullbackOne, e,
      scalarToVecOneContinuousLinearEquiv_apply] using ht
  have hts : e t ∈ tsupport f :=
    subset_tsupport f (by simpa [Function.mem_support] using hne)
  refine ⟨e t, hts, ?_⟩
  change scalarToVecOneContinuousLinearEquiv.symm
      (scalarToVecOneContinuousLinearEquiv t) = t
  exact scalarToVecOneContinuousLinearEquiv.symm_apply_apply t

/-- The compact-support spatial Gagliardo--Nirenberg inequality in dimension
one, in integral-energy form. -/
theorem smooth_one_dimensional_gagliardo_nirenberg_energy
    {f : Vec 1 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    (∫ x, |f x| ^ 6 ∂(volume : Measure (Vec 1))) ≤
      4 * (∫ x, |f x| ^ 2 ∂(volume : Measure (Vec 1))) ^ 2 *
        (∫ x, vecEuclideanNorm (classicalGradient f x) ^ 2
          ∂(volume : Measure (Vec 1))) := by
  let g := scalarPullbackOne f
  have hfC1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := ContDiff.scalarPullbackOne hf
  have hgCompact : HasCompactSupport g := scalarPullbackOne_hasCompactSupport hc
  have hgrad (x : Vec 1) :
      vecEuclideanNorm (classicalGradient f x) =
        |deriv g (vecOneCoordinate x)| := by
    rw [scalarVecEuclideanNorm_fin_one, classicalGradient_apply]
    change |(fderiv ℝ f x) (basisVec 0)| =
      |deriv (scalarPullbackOne f) (vecOneCoordinate x)|
    rw [deriv_scalarPullbackOne_eq_native_directional hfC1
      (vecOneCoordinate x), scalarToVecOne_vecOneCoordinate]
  have hvalue (p : ℕ) :
      (∫ x, |f x| ^ p ∂(volume : Measure (Vec 1))) =
        ∫ t, |g t| ^ p ∂(volume : Measure ℝ) := by
    calc
      _ = ∫ x, |g (vecOneEquivReal x)| ^ p ∂(volume : Measure (Vec 1)) := by
        apply integral_congr_ae
        filter_upwards with x
        change |f x| ^ p =
          |f (scalarToVecOne (vecOneCoordinate x))| ^ p
        rw [scalarToVecOne_vecOneCoordinate]
      _ = ∫ t, |g t| ^ p ∂(volume : Measure ℝ) :=
        volumePreserving_vecOneEquivReal.integral_comp
          vecOneEquivReal.measurableEmbedding (fun t => |g t| ^ p)
  have hgradIntegral :
      (∫ x, vecEuclideanNorm (classicalGradient f x) ^ 2
          ∂(volume : Measure (Vec 1))) =
        ∫ t, |deriv g t| ^ 2 ∂(volume : Measure ℝ) := by
    calc
      _ = ∫ x, |deriv g (vecOneEquivReal x)| ^ 2
          ∂(volume : Measure (Vec 1)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hgrad]
        simp only [vecOneEquivReal_apply]
      _ = ∫ t, |deriv g t| ^ 2 ∂(volume : Measure ℝ) :=
        volumePreserving_vecOneEquivReal.integral_comp
          vecOneEquivReal.measurableEmbedding (fun t => |deriv g t| ^ 2)
  rw [hvalue 6, hvalue 2, hgradIntegral]
  exact smooth_scalar_one_dimensional_gagliardo_nirenberg hg hgCompact

/-- The compact-support one-dimensional estimate in the powered `Lᵖ`-norm
form used when passing to general `H¹` representatives. -/
theorem smooth_one_dimensional_gagliardo_nirenberg_lp_energy
    {f : Vec 1 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    (eLpNorm f 6 volume) ^ 6 ≤
      ENNReal.ofReal 4 * (eLpNorm f 2 volume) ^ 4 *
        (eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x))
          2 volume) ^ 2 := by
  have hfTwo : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    exact hf.continuous.memLp_of_hasCompactSupport hc
  have hfSix : MemLp f (ENNReal.ofReal (6 : ℝ)) volume := by
    exact hf.continuous.memLp_of_hasCompactSupport hc
  have hgradCont : Continuous (fun x => (fderiv ℝ f x) (basisVec (0 : Fin 1))) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradCompact : HasCompactSupport
      (fun x => (fderiv ℝ f x) (basisVec (0 : Fin 1))) :=
    hc.fderiv_apply (𝕜 := ℝ) (basisVec (0 : Fin 1))
  have hgradMem : MemLp
      (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
    have hcoord : MemLp
        (fun x => (fderiv ℝ f x) (basisVec (0 : Fin 1))) 2 volume := by
      exact hgradCont.memLp_of_hasCompactSupport hgradCompact
    have hcoordAbs : MemLp
        (fun x => |(fderiv ℝ f x) (basisVec (0 : Fin 1))|) 2 volume :=
      hcoord.norm
    simpa only [scalarVecEuclideanNorm_fin_one, classicalGradient_apply] using hcoordAbs
  have hvalueTwo := toReal_eLpNorm_two_sq_eq_integral_sq
    (by simpa only [ENNReal.ofReal_ofNat] using hfTwo)
  have hgradTwo := toReal_eLpNorm_two_sq_eq_integral_sq hgradMem
  have hvalueSix := toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
    (p := (6 : ℝ)) (by norm_num) hfSix
  have hvalueTwoAbs : (eLpNorm f 2 volume).toReal ^ 2 =
      ∫ x, |f x| ^ 2 ∂(volume : Measure (Vec 1)) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hvalueTwo
  have hvalueSixAbs : (eLpNorm f 6 volume).toReal ^ 6 =
      ∫ x, |f x| ^ 6 ∂(volume : Measure (Vec 1)) := by
    convert hvalueSix using 1 <;> norm_num [ENNReal.ofReal_ofNat, Real.norm_eq_abs]
  have hgradTwo' :
      (eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x))
        2 volume).toReal ^ 2 =
        ∫ x, vecEuclideanNorm (classicalGradient f x) ^ 2
          ∂(volume : Measure (Vec 1)) := by
    exact hgradTwo
  have hIntegral := smooth_one_dimensional_gagliardo_nirenberg_energy hf hc
  have hreal :
      (eLpNorm f 6 volume).toReal ^ 6 ≤
        4 * (eLpNorm f 2 volume).toReal ^ 4 *
          (eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x))
            2 volume).toReal ^ 2 := by
    calc
      _ = ∫ x, |f x| ^ 6 ∂(volume : Measure (Vec 1)) := hvalueSixAbs
      _ ≤ _ := hIntegral
      _ = _ := by
        rw [← hvalueTwoAbs, ← hgradTwo']
        ring
  have hfSix' : MemLp f 6 volume := by
    simpa only [ENNReal.ofReal_ofNat] using hfSix
  have hfTwo' : MemLp f 2 volume := by
    simpa only [ENNReal.ofReal_ofNat] using hfTwo
  have hleftTop : (eLpNorm f 6 volume) ^ 6 ≠ ∞ :=
    ENNReal.pow_ne_top hfSix'.eLpNorm_ne_top
  have hrightTop :
      ENNReal.ofReal 4 * (eLpNorm f 2 volume) ^ 4 *
          (eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x))
            2 volume) ^ 2 ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.pow_ne_top hfTwo'.eLpNorm_ne_top
    · exact ENNReal.pow_ne_top hgradMem.eLpNorm_ne_top
  have hRealENN :
      ((eLpNorm f 6 volume) ^ 6).toReal ≤
        (ENNReal.ofReal 4 * (eLpNorm f 2 volume) ^ 4 *
          (eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x))
            2 volume) ^ 2).toReal := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 : ℝ)),
      ENNReal.toReal_pow, ENNReal.toReal_pow]
    exact hreal
  exact (ENNReal.toReal_le_toReal hleftTop hrightTop).1 hRealENN

theorem smooth_two_dimensional_gagliardo_nirenberg
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    (eLpNorm f 4 volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) *
        eLpNorm f 2 volume *
          eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
  let F : Vec 2 → ℝ := fun x => f x * f x
  have hFdiff : ContDiff ℝ 1 F := by
    exact (hf.mul hf).of_le (by norm_num)
  have hFcompact : HasCompactSupport F := hc.mul_right
  have hderiv (i : Fin 2) (x : Vec 2) :
      (fderiv ℝ F x) (basisVec i) =
        (2 : ℝ) * f x * (fderiv ℝ f x) (basisVec i) := by
    have hdiff := fderiv_mul
      (hf.differentiable (by simp) x)
      (hf.differentiable (by simp) x)
    rw [show F = f * f by rfl, hdiff]
    simp only [add_apply, smul_apply]
    ring
  have hSob := eLpNorm_sobolevConjugate_le_sum_eLpNorm_fderiv_apply_basisVec
    (d := 2) (by norm_num) (p := 1) (by norm_num) (by norm_num)
    hFdiff hFcompact
  have hcoord : ∀ i : Fin 2,
      eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) 2 volume ≤
        eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
    intro i
    have hcoordCont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    apply eLpNorm_mono hcoordCont.aestronglyMeasurable
    intro x
    change |(fderiv ℝ f x) (basisVec i)| ≤
      |vecEuclideanNorm (classicalGradient f x)|
    rw [abs_of_nonneg (vecEuclideanNorm_nonneg _)]
    exact abs_apply_le_vecEuclideanNorm (classicalGradient f x) i
  have hsum :
      (∑ i : Fin 2,
        eLpNorm (fun x => (fderiv ℝ F x) (basisVec i)) 1 volume) ≤
        ENNReal.ofReal 4 * eLpNorm f 2 volume *
          eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
    calc
      _ = ∑ i : Fin 2,
          eLpNorm (fun x => (2 : ℝ) * f x * (fderiv ℝ f x) (basisVec i))
            1 volume := by
        refine Finset.sum_congr rfl fun i _ => ?_
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun x => hderiv i x
      _ ≤ ∑ i : Fin 2,
          ENNReal.ofReal 2 * eLpNorm f 2 volume *
            eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) 2 volume := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact eLpNorm_double_mul_le
          hf.continuous.aestronglyMeasurable
          ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
      _ ≤ ∑ _i : Fin 2,
          ENNReal.ofReal 2 * eLpNorm f 2 volume *
            eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        exact hcoord i
      _ = ENNReal.ofReal 4 * eLpNorm f 2 volume *
          eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_ofNat, ← mul_assoc]
        norm_num
  have heq : eLpNorm F 2 volume = (eLpNorm f 4 volume) ^ (2 : ℝ) := by
    have hrpow := eLpNorm_norm_rpow (f := f) (μ := volume)
      hf.continuous.aestronglyMeasurable
      (p := (2 : ℝ≥0∞)) (q := 2) (by norm_num)
    have hfun : (fun x => ‖f x‖ ^ (2 : ℝ)) = F := by
      funext x
      simp [F, Real.norm_eq_abs, sq_abs]
      ring
    rw [hfun] at hrpow
    have hp : 2 * ENNReal.ofReal (2 : ℝ) = 4 := by norm_num
    rw [hp] at hrpow
    exact hrpow
  have hSob' : eLpNorm F 2 volume ≤
      ENNReal.ofReal (sobolevOneConstant 2 : ℝ) *
        ∑ i : Fin 2, eLpNorm (fun x => (fderiv ℝ F x) (basisVec i)) 1 volume := by
    convert hSob using 1 <;> norm_num [sobolevConjugate, ENNReal.ofReal_coe_nnreal]
  calc
    (eLpNorm f 4 volume) ^ (2 : ℝ) = eLpNorm F 2 volume := heq.symm
    _ ≤ ENNReal.ofReal (sobolevOneConstant 2 : ℝ) *
          ∑ i : Fin 2, eLpNorm (fun x => (fderiv ℝ F x) (basisVec i)) 1 volume := hSob'
    _ ≤ ENNReal.ofReal (sobolevOneConstant 2 : ℝ) *
          (ENNReal.ofReal 4 * eLpNorm f 2 volume *
            eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume) := by
      gcongr
    _ = ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) *
          eLpNorm f 2 volume *
            eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
      have hcoe :
          ENNReal.ofReal (sobolevOneConstant 2 : ℝ) * ENNReal.ofReal 4 =
            ENNReal.ofReal (4 * (sobolevOneConstant 2 : ℝ)) := by
        calc
          _ = ENNReal.ofReal ((sobolevOneConstant 2 : ℝ) * 4) :=
            (ENNReal.ofReal_mul (by positivity)).symm
          _ = _ := by congr 1; ring
      calc
        _ = (ENNReal.ofReal (sobolevOneConstant 2 : ℝ) * ENNReal.ofReal 4) *
              eLpNorm f 2 volume *
              eLpNorm (fun x => vecEuclideanNorm (classicalGradient f x)) 2 volume := by
          ring
        _ = _ := by rw [hcoe]

end PDE.Parabolic
