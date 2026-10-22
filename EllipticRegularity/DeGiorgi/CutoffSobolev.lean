module

public import EllipticRegularity.Energy.CaccioppoliIntegrated
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Sobolev.H1.CutoffEnergy
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolevPower

/-!
# Cutoff Sobolev estimate for De Giorgi truncations

This module is the first `d ≥ 3` De Giorgi composition.  It joins the
zero-boundary critical Sobolev estimate to the integrated Caccioppoli bound
for `η (u-k)₊`.  The cutoff-gradient error is kept on the declared outer
set, so neither the domain nor an unquantified enlargement enters the
constant.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

private theorem setIntegral_positivePart_sq_mul_cutoff_gradient_le
    {d : ℕ} {K k : ℝ} {U inner outer : Set (Vec d)}
    {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    (∫ x in U, max (u x - k) 0 ^ 2 *
        vecNormSq (classicalGradient η.toFun x)) ≤
      K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by
  let w : Vec d → ℝ := fun x => max (u x - k) 0
  let G : Vec d → Vec d := fun x => w x • classicalGradient η.toFun x
  have hw : MemL2On U w := by
    simpa only [w, H1Function.positivePartSubConst_toFun] using
      (u.positivePartSubConst hU k).memL2
  have hDηTop (i : Fin d) : MemLpOn U ∞
      (fun x => classicalGradient η.toFun x i) :=
    W1pFunction.cutoff_gradient_memLpTop η i
  have hG : MemVectorL2On U G := by
    intro i
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using
      hw.fun_mul (hDηTop i)
  have hgradientInt : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hG
    simpa only [G, vecNormSq_smul] using hraw
  have hwSqInt : IntegrableOn (fun x => w x ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hw hw
  have hgradientRestrict :
      (∫ x in U, w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) =
        ∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet houter fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, pow_two, mul_zero]
  have hgradientOuter : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) outer :=
    hgradientInt.mono_set houter
  have hKSqOuter : IntegrableOn (fun x => K ^ 2 * w x ^ 2) outer :=
    (hwSqInt.mono_set houter).const_mul (K ^ 2)
  have hgradientLe :
      (∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
        K ^ 2 * ∫ x in outer, w x ^ 2 := by
    calc
      (∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
          ∫ x in outer, K ^ 2 * w x ^ 2 := by
        apply integral_mono_ae hgradientOuter hKSqOuter
        exact Filter.Eventually.of_forall fun x => by
          have hgradSq :
              vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
            calc
              vecNormSq (classicalGradient η.toFun x) =
                  vecEuclideanNorm (classicalGradient η.toFun x) ^ 2 :=
                (vecEuclideanNorm_sq _).symm
              _ ≤ K ^ 2 :=
                pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
                  (η.gradient_bound x) 2
          calc
            w x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤
                w x ^ 2 * K ^ 2 :=
              mul_le_mul_of_nonneg_left hgradSq (sq_nonneg (w x))
            _ = K ^ 2 * w x ^ 2 := by ring
      _ = K ^ 2 * ∫ x in outer, w x ^ 2 :=
        integral_const_mul (K ^ 2) _
  calc
    (∫ x in U, max (u x - k) 0 ^ 2 *
        vecNormSq (classicalGradient η.toFun x)) =
        ∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by rfl
    _ = ∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := hgradientRestrict
    _ ≤ K ^ 2 * ∫ x in outer, w x ^ 2 := hgradientLe
    _ = K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by rfl

/-- The critical cutoff Sobolev estimate for a divergence-form subsolution.
The constants are literal: the `8 * Lam / lam` is twice the weighted
Caccioppoli constant, while the final `2` is the cutoff-product error. -/
theorem setIntegral_abs_cutoff_mul_positivePartSubConst_rpow_two_div_le_of_h10Subharmonic
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    (∫ x in U,
        |η x * max (u x - k) 0| ^ (sobolevConjugate d 2)) ^
        (2 / sobolevConjugate d 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2 := by
  let w : H1Function U := u.positivePartSubConst hU k
  let v : H10Function U := w.mulCutoffToH10 hU η houter
  have hSob :=
    setIntegral_abs_rpow_sobolevConjugate_two_rpow_two_div_le hd v
  have hCaccioppoli :=
    caccioppoli_integrated_positivePart_gradient_of_h10Subharmonic
      (k := k) hU hEll hlam hsub η houter
  have hCutoffError :=
    setIntegral_positivePart_sq_mul_cutoff_gradient_le
      (u := u) (k := k) hU η houter
  have hratio_nonneg : 0 ≤ 4 * Lam / lam :=
    div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
  have hweighted :
      (∫ x in U, η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
        (4 * Lam / lam) *
          (K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2) := by
    calc
      (∫ x in U, η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
          (4 * Lam / lam) * ∫ x in U,
            max (u x - k) 0 ^ 2 *
              vecNormSq (classicalGradient η.toFun x) :=
        hCaccioppoli
      _ ≤ (4 * Lam / lam) *
          (K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2) :=
        mul_le_mul_of_nonneg_left hCutoffError hratio_nonneg
  have henergy :
      (∫ x in U, vecNormSq (v.toH1Function.grad x)) ≤
        2 * (∫ x in U, η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x)) +
          2 * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by
    simpa only [v, w, H1Function.positivePartSubConst_grad] using!
      H1Function.setIntegral_vecNormSq_mulCutoffToH10_grad_le w η hU houter
  have henergyFinal :
      (∫ x in U, vecNormSq (v.toH1Function.grad x)) ≤
        ((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2 := by
    calc
      (∫ x in U, vecNormSq (v.toH1Function.grad x)) ≤
          2 * (∫ x in U, η x ^ 2 *
            vecNormSq ({y | k < u y}.indicator u.grad x)) +
            2 * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := henergy
      _ ≤ 2 * ((4 * Lam / lam) *
            (K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2)) +
            2 * K ^ 2 * ∫ x in outer, max (u x - k) 0 ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hweighted
            (show (0 : ℝ) ≤ 2 by norm_num)) (le_refl _)
      _ = ((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2 := by ring
  calc
    (∫ x in U,
        |η x * max (u x - k) 0| ^ (sobolevConjugate d 2)) ^
        (2 / sobolevConjugate d 2) =
        (∫ x in U, |v.toFun x| ^ (sobolevConjugate d 2)) ^
          (2 / sobolevConjugate d 2) := by
      rw [H1Function.mulCutoffToH10_toFun,
        H1Function.positivePartSubConst_toFun]
    _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ∫ x in U, vecNormSq (v.grad x) := hSob
    _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        (((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2) :=
      mul_le_mul_of_nonneg_left henergyFinal (sq_nonneg _)
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2 := by ring

/-- Homogeneous-solution wrapper for the critical cutoff Sobolev estimate. -/
theorem setIntegral_abs_cutoff_mul_positivePartSubConst_rpow_two_div_le
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    (∫ x in U,
        |η x * max (u x - k) 0| ^ (sobolevConjugate d 2)) ^
        (2 / sobolevConjugate d 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2 :=
  setIntegral_abs_cutoff_mul_positivePartSubConst_rpow_two_div_le_of_h10Subharmonic
    (k := k) hd hU hEll hlam hLam (hsol.toH10SubharmonicOn hEll) η houter

/-- The cutoff Sobolev estimate in the exponent form consumed directly by
the De Giorgi level-set recurrence. -/
theorem setIntegral_abs_cutoff_mul_positivePartSubConst_rpow_sub_div_le_of_h10Subharmonic
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    (∫ x in U,
        |η x * max (u x - k) 0| ^
          ((2 : ℝ) * d / ((d : ℝ) - 2))) ^
        (((d : ℝ) - 2) / (d : ℝ)) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * K ^ 2 *
          ∫ x in outer, max (u x - k) 0 ^ 2 := by
  rw [← two_div_sobolevConjugate_two hd]
  simpa only [sobolevConjugate, mul_comm] using
    setIntegral_abs_cutoff_mul_positivePartSubConst_rpow_two_div_le_of_h10Subharmonic
      (k := k) hd hU hEll hlam hLam hsub η houter

/-- The critical De Giorgi cutoff estimate on concentric Euclidean balls.
The inner integral is obtained from the cutoff plateau before the critical
power is taken; in particular, no unverified finiteness convention for a
set integral is used. -/
theorem setIntegral_positivePartSubConst_rpow_ball_le_of_h10Subharmonic
    {d : ℕ} {lam Lam k r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u) :
    (∫ x in euclideanBall x₀ r,
        max (u x - k) 0 ^ ((2 : ℝ) * d / ((d : ℝ) - 2))) ^
        (((d : ℝ) - 2) / (d : ℝ)) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 := by
  let η : QuantitativeSmoothCutoff
      (euclideanBall x₀ r) (euclideanBall x₀ R) (32 / (R - r)) :=
    quantitativeBallCutoff x₀ hr.le hrR
  let w : H1Function U := u.positivePartSubConst hU k
  let v : H10Function U := w.mulCutoffToH10 hU η hball
  let q : ℝ := sobolevConjugate d 2
  have hq : 0 < q := by
    dsimp [q]
    apply sobolevConjugate_pos (by norm_num)
    exact_mod_cast hd
  have hGradMem :
      MemLp (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn U) :=
    v.gradMemL2.memLp_vecEuclideanNorm
  have hGradNorm_ne_top :
      euclideanFieldELpNormOn U 2 v.grad ≠ ∞ := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn] using
      hGradMem.eLpNorm_ne_top
  have hSobRaw :=
    eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn hd v
  have hvMem : MemLp v.toFun (ENNReal.ofReal q) (volumeOn U) := by
    apply lt_of_le_of_lt (by
      simpa only [eLpNormOn, q, volumeOn] using hSobRaw)
    exact lt_top_iff_ne_top.mpr <|
      ENNReal.mul_ne_top ENNReal.coe_ne_top hGradNorm_ne_top
  have hValueInt : IntegrableOn (fun x => |v.toFun x| ^ q) U := by
    have h := hvMem.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    simpa only [volumeOn, Real.norm_eq_abs,
      ENNReal.toReal_ofReal hq.le] using! h
  have hvValue : v.toFun = fun x => η x * max (u x - k) 0 := by
    dsimp only [v, w]
    rw [H1Function.mulCutoffToH10_toFun,
      H1Function.positivePartSubConst_toFun]
  have hinnerU : euclideanBall x₀ r ⊆ U :=
    (euclideanBall_mono hr.le hrR.le).trans hball
  have hinnerEq :
      (∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ q) =
        ∫ x in euclideanBall x₀ r, |v.toFun x| ^ q := by
    apply MeasureTheory.setIntegral_congr_fun
      (isOpen_euclideanBall x₀ r).measurableSet
    intro x hx
    rw [hvValue]
    change max (u x - k) 0 ^ q =
      |η x * max (u x - k) 0| ^ q
    rw [η.eq_one_on_inner x hx]
    have hpositive : 0 ≤ max (u x - k) 0 := le_max_right _ _
    simp only [one_mul, abs_of_nonneg hpositive]
  have hinnerLe :
      (∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ q) ≤
        ∫ x in U, |v.toFun x| ^ q := by
    rw [hinnerEq]
    apply MeasureTheory.setIntegral_mono_set hValueInt
    · exact Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (abs_nonneg (v.toFun x)) _
    · exact Filter.Eventually.of_forall fun x hx => hinnerU hx
  have hinnerNonneg :
      0 ≤ ∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ q := by
    apply MeasureTheory.setIntegral_nonneg
      (isOpen_euclideanBall x₀ r).measurableSet
    intro x _
    exact Real.rpow_nonneg (le_max_right _ _) _
  have halpha : 0 ≤ ((d : ℝ) - 2) / (d : ℝ) := by
    apply div_nonneg
    · apply sub_nonneg.mpr
      exact_mod_cast (by omega : 2 ≤ d)
    · positivity
  have hinnerPow :
      (∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ q) ^
          (((d : ℝ) - 2) / (d : ℝ)) ≤
        (∫ x in U, |v.toFun x| ^ q) ^
          (((d : ℝ) - 2) / (d : ℝ)) :=
    Real.rpow_le_rpow hinnerNonneg hinnerLe halpha
  have hCutoff :=
    setIntegral_abs_cutoff_mul_positivePartSubConst_rpow_sub_div_le_of_h10Subharmonic
      (k := k) hd hU hEll hlam hLam hsub η hball
  calc
    (∫ x in euclideanBall x₀ r,
        max (u x - k) 0 ^ ((2 : ℝ) * d / ((d : ℝ) - 2))) ^
        (((d : ℝ) - 2) / (d : ℝ)) =
        (∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ q) ^
          (((d : ℝ) - 2) / (d : ℝ)) := by
      simp only [q, sobolevConjugate, mul_comm]
    _ ≤ (∫ x in U, |v.toFun x| ^ q) ^
          (((d : ℝ) - 2) / (d : ℝ)) := hinnerPow
    _ = (∫ x in U,
          |η x * max (u x - k) 0| ^ (sobolevConjugate d 2)) ^
          (((d : ℝ) - 2) / (d : ℝ)) := by
      rw [hvValue]
    _ ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2 := by
      simpa only [sobolevConjugate, mul_comm] using hCutoff

end PDE
