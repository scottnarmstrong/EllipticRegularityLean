module

public import EllipticRegularity.Energy.CaccioppoliPointwise
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# Integrated subsolution Caccioppoli estimate

This module combines the all-`H¹₀` weak-subsolution formulation with the
literal nonnegative test `η² (u-k)₊`. It retains the nonsymmetric coefficient
convention and proves integrability of every energy term before using its
integral. Homogeneous weak solutions are exported as corollaries.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open MeasureTheory

private theorem vecDot_smul_right {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem vecDot_add_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem matVecMul_zero {d : ℕ} (A : Mat d) :
    matVecMul A (0 : Vec d) = 0 := by
  funext i
  simp only [matVecMul_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem integrableOn_const_mul {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : IntegrableOn f U) (c : ℝ) :
    IntegrableOn (fun x => c * f x) U :=
  hf.const_mul c

/-- The subsolution Caccioppoli estimate obtained by testing with the exact
nonnegative `H¹₀` representative `η² (u-k)₊`.

Every coefficient and exponent remains literal in the public statement. -/
theorem caccioppoli_integrated_positivePart_of_h10Subharmonic
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U,
        η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
          (matVecMul (a x) ({y | k < u y}.indicator u.grad x)) ≤
      4 * Lam * ∫ x in U,
        max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
  let w : Vec d → ℝ := fun x => max (u x - k) 0
  let ξ : Vec d → Vec d := fun x => {y | k < u y}.indicator u.grad x
  let G : Vec d → Vec d := fun x => w x • classicalGradient η.toFun x
  let C : Vec d → Vec d := fun x => (2 * η x) • G x
  let Egrad : Vec d → Vec d := fun x => η x ^ 2 • ξ x
  let φ : H10Function U :=
    H1Function.mulCutoffSqPositivePartSubConstToH10 hU u k η houter
  have hφgrad : φ.toH1Function.grad = fun x => Egrad x + C x := by
    rw [show φ = H1Function.mulCutoffSqPositivePartSubConstToH10 hU u k η houter from rfl,
      H1Function.mulCutoffSqPositivePartSubConstToH10_grad]
    funext x
    ext i
    simp only [Egrad, C, G, ξ, w, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hηTop : MemLpOn U ∞ η.toFun :=
    W1pFunction.cutoff_memLpTop η
  have hDηTop (i : Fin d) : MemLpOn U ∞
      (fun x => classicalGradient η.toFun x i) :=
    W1pFunction.cutoff_gradient_memLpTop η i
  have hw : MemL2On U w := by
    simpa only [w, H1Function.positivePartSubConst_toFun] using
      (u.positivePartSubConst hU k).memL2
  have hG : MemVectorL2On U G := by
    intro i
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using hw.fun_mul (hDηTop i)
  have hC : MemVectorL2On U C := by
    intro i
    have hmul : MemL2On U (fun x => η x * G x i) := hηTop.fun_mul (hG i)
    simpa only [C, G, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm] using! hmul.const_smul (2 : ℝ)
  have hφL2 : MemVectorL2On U φ.toH1Function.grad := φ.toH1Function.gradMemL2
  have hEgrad : MemVectorL2On U Egrad := by
    intro i
    have hsub := (hφL2 i).sub (hC i)
    have hpoint : (fun x => Egrad x i) =
        fun x => φ.toH1Function.grad x i - C x i := by
      funext x
      rw [hφgrad]
      simp only [Pi.add_apply]
      ring
    rw [hpoint]
    exact hsub
  have hflux : MemVectorL2On U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  have hmainInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (Egrad x)) U :=
    integrableOn_vecDot_of_memVectorL2On hflux hEgrad
  have hcrossInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (C x)) U :=
    integrableOn_vecDot_of_memVectorL2On hflux hC
  have hmain_eq :
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (Egrad x)) =
        fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    funext x
    by_cases hx : k < u x
    · have hxi : ξ x = u.grad x := by
        exact Set.indicator_of_mem (s := {y : Vec d | k < u y}) (f := u.grad) hx
      have hEgrad : Egrad x = η x ^ 2 • u.grad x := by
        simp only [Egrad, hxi]
      rw [hxi, hEgrad]
      rw [vecDot_smul_right, vecDot_comm]
    · have hxi : ξ x = 0 := by
        exact Set.indicator_of_notMem (s := {y : Vec d | k < u y}) (f := u.grad) hx
      have hEgrad : Egrad x = 0 := by simp only [Egrad, hxi, smul_zero]
      rw [hxi, hEgrad]
      simp only [vecDot, matVecMul_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hcross_eq :
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (C x)) =
        fun x => 2 * η x * w x *
          vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x) := by
    funext x
    by_cases hx : k < u x
    · have hxi : ξ x = u.grad x := by
        exact Set.indicator_of_mem (s := {y : Vec d | k < u y}) (f := u.grad) hx
      rw [hxi, show C x = (2 * η x) • (w x • classicalGradient η.toFun x) by
          simp only [C, G],
        vecDot_smul_right, vecDot_smul_right]
      ring
    · have hwzero : w x = 0 := by
        dsimp only [w]
        exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hx))
      have hxi : ξ x = 0 := by
        exact Set.indicator_of_notMem (s := {y : Vec d | k < u y}) (f := u.grad) hx
      have hCzero : C x = 0 := by
        ext i
        simp only [C, G, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [hwzero]
        ring
      rw [hwzero, hxi, hCzero]
      simp only [vecDot, matVecMul_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      ring
  have hmain : IntegrableOn
      (fun x => η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    rw [← hmain_eq]
    exact hmainInt
  have hcross : IntegrableOn
      (fun x => 2 * η x * w x *
        vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)) U := by
    rw [← hcross_eq]
    exact hcrossInt
  have hGsq : IntegrableOn (fun x => vecNormSq (G x)) U := by
    simpa only [vecNormSq] using integrableOn_vecDot_of_memVectorL2On hG hG
  have hrhs : IntegrableOn (fun x => 2 * Lam * vecNormSq (G x)) U := by
    simpa only [mul_assoc] using integrableOn_const_mul hGsq (2 * Lam)
  have hφNonnegative : φ.AENonnegative := by
    apply H10Function.aeNonnegative_of_forall
    intro x
    change 0 ≤ η x ^ 2 * max (u x - k) 0
    exact mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have htest := hsub φ hφNonnegative
  have hweak :
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) ≤ 0 := by
    simpa only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
      integral_zero, sub_zero] using htest.2
  have hsum :
      (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
        ∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (ξ x))
            (classicalGradient η.toFun x) ≤ 0 := by
    calc
      (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) +
          ∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x) =
          (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (Egrad x)) +
            ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (C x) := by
              rw [hmain_eq, hcross_eq]
      _ = ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (Egrad x) +
            vecDot (matVecMul (a x) (u.grad x)) (C x) :=
              (MeasureTheory.integral_add hmainInt hcrossInt).symm
      _ = ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
            (φ.toH1Function.grad x) := by
              apply integral_congr_ae
              filter_upwards with x
              rw [hφgrad, vecDot_add_right]
      _ ≤ 0 := hweak
  have hmem : ∀ᵐ x ∂volumeOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff'
      (measurableSet_of_isEllipticFieldOn hEll)).2
      (Filter.Eventually.of_forall fun x hx => hx)
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      |2 * η x * w x * vecDot (matVecMul (a x) (ξ x))
        (classicalGradient η.toFun x)| ≤
        (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
          2 * Lam * vecNormSq (G x) := by
    filter_upwards [hmem] with x hx
    have hpoint := abs_two_mul_mul_vecDot_matVecMul_le_caccioppoli
      (eta := η x) (w := w x) (hEll.2 x hx) (ξ x)
        (classicalGradient η.toFun x)
    simpa only [G, vecNormSq_smul, mul_assoc, mul_left_comm, mul_comm] using hpoint
  have habs : IntegrableOn (fun x =>
      |2 * η x * w x * vecDot (matVecMul (a x) (ξ x))
        (classicalGradient η.toFun x)|) U :=
    hcross.abs
  have hhalf : IntegrableOn (fun x =>
      (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2) U :=
    hmain.div_const 2
  have hboundInt : IntegrableOn (fun x =>
      (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
        2 * Lam * vecNormSq (G x)) U :=
    hhalf.add hrhs
  have hbound := MeasureTheory.integral_mono_ae habs hboundInt hpointwise
  have habsIntegral :
      |∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)| ≤
        ∫ x in U, |2 * η x * w x *
          vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)| :=
    MeasureTheory.abs_integral_le_integral_abs
  have hmain_le_abs :
      ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) ≤
        |∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)| := by
    calc
      ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) ≤
          -(∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)) := by
              linarith [hsum]
      _ ≤ |∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)| := neg_le_abs _
  have hmain_le :
      ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) ≤
        (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
          ∫ x in U, 2 * Lam * vecNormSq (G x) := by
    calc
      ∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) ≤
          |∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)| := hmain_le_abs
      _ ≤ ∫ x in U, |2 * η x * w x *
            vecDot (matVecMul (a x) (ξ x)) (classicalGradient η.toFun x)| := habsIntegral
      _ ≤ ∫ x in U,
          (η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
            2 * Lam * vecNormSq (G x) := hbound
      _ = (∫ x in U, η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) / 2 +
          ∫ x in U, 2 * Lam * vecNormSq (G x) := by
            rw [MeasureTheory.integral_add hhalf hrhs, MeasureTheory.integral_div]
  have hrhs_eq :
      (∫ x in U, 2 * Lam * vecNormSq (G x)) =
        2 * Lam * ∫ x in U, vecNormSq (G x) :=
    MeasureTheory.integral_const_mul (2 * Lam) _
  have hfinal :
      (∫ x in U, η x ^ 2 * vecDot (ξ x)
        (matVecMul (a x) (ξ x))) ≤
        4 * Lam * ∫ x in U, vecNormSq (G x) := by
    rw [hrhs_eq] at hmain_le
    linarith
  simpa only [G, vecNormSq_smul] using hfinal

/-- A homogeneous weak solution satisfies the same integrated positive-part
Caccioppoli estimate through its all-`H¹₀` subsolution interface. -/
theorem caccioppoli_integrated_positivePart
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U,
        η x ^ 2 * vecDot ({y | k < u y}.indicator u.grad x)
          (matVecMul (a x) ({y | k < u y}.indicator u.grad x)) ≤
      4 * Lam * ∫ x in U,
        max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x) :=
  caccioppoli_integrated_positivePart_of_h10Subharmonic
    (k := k) hU hEll (hsol.toH10SubharmonicOn hEll) η houter

/-- Coercivity converts the energy estimate into the weighted gradient
Caccioppoli estimate with the explicit ellipticity ratio `4 * Lam / lam`. -/
theorem caccioppoli_integrated_positivePart_gradient_of_h10Subharmonic
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U,
        η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * ∫ x in U,
        max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
  let ξ : Vec d → Vec d :=
    fun x => {y | k < u y}.indicator u.grad x
  have hξ : MemVectorL2On U ξ := by
    simpa only [ξ, H1Function.positivePartSubConst_grad] using
      (u.positivePartSubConst hU k).gradMemL2
  have hηSqTop : MemLpOn U ∞ η.sq.toFun :=
    W1pFunction.cutoff_memLpTop η.sq
  have hηSqξ : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
    intro i
    simpa only [QuantitativeSmoothCutoff.sq_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm] using
      (hξ i).fun_mul hηSqTop
  have hgradInt :
      IntegrableOn (fun x => η x ^ 2 * vecNormSq (ξ x)) U := by
    have hraw :=
      integrableOn_vecDot_of_memVectorL2On hξ hηSqξ
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      change vecDot (ξ x) (η x ^ 2 • ξ x) =
        η x ^ 2 * vecNormSq (ξ x)
      rw [vecDot_smul_right]
      rfl
  have hfluxξ :
      MemVectorL2On U (fun x => matVecMul (a x) (ξ x)) :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll hξ
  have henergyInt :
      IntegrableOn
        (fun x => η x ^ 2 *
          vecDot (ξ x) (matVecMul (a x) (ξ x))) U := by
    have hraw :=
      integrableOn_vecDot_of_memVectorL2On hfluxξ hηSqξ
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      change vecDot (matVecMul (a x) (ξ x)) (η x ^ 2 • ξ x) =
        η x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))
      rw [vecDot_smul_right,
        vecDot_comm (matVecMul (a x) (ξ x)) (ξ x)]
  have hleftInt :
      IntegrableOn
        (fun x => lam * (η x ^ 2 * vecNormSq (ξ x))) U :=
    hgradInt.const_mul lam
  have hcoerciveIntegral :
      (∫ x in U, lam * (η x ^ 2 * vecNormSq (ξ x))) ≤
        ∫ x in U, η x ^ 2 *
          vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    exact MeasureTheory.setIntegral_mono_on hleftInt henergyInt
      hU.measurableSet fun x hx => by
        simpa only [mul_assoc] using
          mul_sq_vecNormSq_le_sq_mul_energy_of_isEllipticMatrix
            (hEll.elliptic hx) (ξ x) (eta := η x)
  have hcoercive :
      lam * (∫ x in U, η x ^ 2 * vecNormSq (ξ x)) ≤
        ∫ x in U, η x ^ 2 *
          vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    calc
      lam * (∫ x in U, η x ^ 2 * vecNormSq (ξ x)) =
          ∫ x in U, lam * (η x ^ 2 * vecNormSq (ξ x)) := by
            symm
            exact MeasureTheory.integral_const_mul lam _
      _ ≤ ∫ x in U, η x ^ 2 *
          vecDot (ξ x) (matVecMul (a x) (ξ x)) :=
        hcoerciveIntegral
  have henergy :=
    caccioppoli_integrated_positivePart_of_h10Subharmonic
      (k := k) hU hEll hsub η houter
  have hcombined :
      lam * (∫ x in U, η x ^ 2 * vecNormSq (ξ x)) ≤
        4 * Lam * ∫ x in U,
          max (u x - k) 0 ^ 2 *
            vecNormSq (classicalGradient η.toFun x) :=
    hcoercive.trans henergy
  change (∫ x in U, η x ^ 2 * vecNormSq (ξ x)) ≤ _
  rw [show
    (4 * Lam / lam) * (∫ x in U,
        max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) =
      (4 * Lam * (∫ x in U,
        max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x))) / lam by ring]
  apply (le_div_iff₀ hlam).2
  nlinarith [hcombined]

/-- Homogeneous-solution wrapper for the weighted gradient estimate. -/
theorem caccioppoli_integrated_positivePart_gradient
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U,
        η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * ∫ x in U,
        max (u x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x) :=
  caccioppoli_integrated_positivePart_gradient_of_h10Subharmonic
    (k := k) hU hEll hlam (hsol.toH10SubharmonicOn hEll) η houter

/-- Bounding the cutoff gradient by its declared constant `K` gives the
fully scalar weighted Caccioppoli estimate. -/
theorem
    caccioppoli_integrated_positivePart_gradient_bound_of_h10Subharmonic
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U,
        η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * K ^ 2 * ∫ x in U,
        max (u x - k) 0 ^ 2 := by
  let w : Vec d → ℝ := fun x => max (u x - k) 0
  let G : Vec d → Vec d :=
    fun x => w x • classicalGradient η.toFun x
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
  have hQInt :
      IntegrableOn
        (fun x => w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hG
    simpa only [G, vecNormSq_smul] using hraw
  have hwSqInt : IntegrableOn (fun x => w x ^ 2) U := by
    simpa only [pow_two] using
      integrableOn_mul_of_memL2On hw hw
  have hKSqInt : IntegrableOn (fun x => K ^ 2 * w x ^ 2) U :=
    hwSqInt.const_mul (K ^ 2)
  have hQle :
      (∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
        K ^ 2 * ∫ x in U, w x ^ 2 := by
    calc
      (∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
          ∫ x in U, K ^ 2 * w x ^ 2 := by
            exact MeasureTheory.setIntegral_mono_on hQInt hKSqInt
              hU.measurableSet fun x _hx => by
                have hgradSq :
                    vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
                  calc
                    vecNormSq (classicalGradient η.toFun x) =
                        vecEuclideanNorm
                            (classicalGradient η.toFun x) ^ 2 :=
                      (vecEuclideanNorm_sq _).symm
                    _ ≤ K ^ 2 :=
                      pow_le_pow_left₀
                        (vecEuclideanNorm_nonneg _)
                        (η.gradient_bound x) 2
                calc
                  w x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤
                      w x ^ 2 * K ^ 2 :=
                    mul_le_mul_of_nonneg_left hgradSq (sq_nonneg (w x))
                  _ = K ^ 2 * w x ^ 2 := by ring
      _ = K ^ 2 * ∫ x in U, w x ^ 2 :=
        MeasureTheory.integral_const_mul (K ^ 2) _
  have hbase :=
    caccioppoli_integrated_positivePart_gradient_of_h10Subharmonic
      (k := k) hU hEll hlam hsub η houter
  have hcoefficient : 0 ≤ 4 * Lam / lam :=
    div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
  change (∫ x in U,
      η x ^ 2 * vecNormSq ({y | k < u y}.indicator u.grad x)) ≤ _
  calc
    (∫ x in U,
        η x ^ 2 * vecNormSq ({y | k < u y}.indicator u.grad x)) ≤
        (4 * Lam / lam) * ∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
      simpa only [w] using hbase
    _ ≤ (4 * Lam / lam) * (K ^ 2 * ∫ x in U, w x ^ 2) :=
      mul_le_mul_of_nonneg_left hQle hcoefficient
    _ = (4 * Lam / lam) * K ^ 2 * ∫ x in U,
        max (u x - k) 0 ^ 2 := by
      simp only [w]
      ring

/-- Homogeneous-solution wrapper for the cutoff-gradient-bound estimate. -/
theorem caccioppoli_integrated_positivePart_gradient_bound
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in U,
        η x ^ 2 *
          vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * K ^ 2 * ∫ x in U,
        max (u x - k) 0 ^ 2 :=
  caccioppoli_integrated_positivePart_gradient_bound_of_h10Subharmonic
    (k := k) hU hEll hlam hLam (hsol.toH10SubharmonicOn hEll) η houter

/-- Geometry-free cutoff form: the cutoff plateau controls the positive-part
gradient on `inner`, while cutoff support localizes the value term to
`outer`. -/
theorem caccioppoli_positivePart_on_inner_of_h10Subharmonic
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hinnerMeas : MeasurableSet inner)
    (houterMeas : MeasurableSet outer)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in inner,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * K ^ 2 * ∫ x in outer,
        max (u x - k) 0 ^ 2 := by
  let w : Vec d → ℝ := fun x => max (u x - k) 0
  let ξ : Vec d → Vec d :=
    fun x => {y | k < u y}.indicator u.grad x
  let G : Vec d → Vec d :=
    fun x => w x • classicalGradient η.toFun x
  have hξ : MemVectorL2On U ξ := by
    simpa only [ξ, H1Function.positivePartSubConst_grad] using
      (u.positivePartSubConst hU k).gradMemL2
  have hηSqTop : MemLpOn U ∞ η.sq.toFun :=
    W1pFunction.cutoff_memLpTop η.sq
  have hηSqξ : MemVectorL2On U (fun x => η x ^ 2 • ξ x) := by
    intro i
    simpa only [QuantitativeSmoothCutoff.sq_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm] using
      (hξ i).fun_mul hηSqTop
  have hweightedInt :
      IntegrableOn (fun x => η x ^ 2 * vecNormSq (ξ x)) U := by
    have hraw :=
      integrableOn_vecDot_of_memVectorL2On hξ hηSqξ
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      change vecDot (ξ x) (η x ^ 2 • ξ x) =
        η x ^ 2 * vecNormSq (ξ x)
      rw [vecDot_smul_right]
      rfl
  have hinnerU : inner ⊆ U :=
    η.inner_subset_outer.trans houter
  have hinnerWeighted :
      (∫ x in inner, vecNormSq (ξ x)) =
        ∫ x in inner, η x ^ 2 * vecNormSq (ξ x) := by
    exact MeasureTheory.setIntegral_congr_fun hinnerMeas fun x hx => by
      rw [η.eq_one_on_inner x hx]
      ring
  have hinnerLe :
      (∫ x in inner, vecNormSq (ξ x)) ≤
        ∫ x in U, η x ^ 2 * vecNormSq (ξ x) := by
    rw [hinnerWeighted]
    exact MeasureTheory.setIntegral_mono_set hweightedInt
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg (η x)) (vecNormSq_nonneg (ξ x)))
      (Filter.Eventually.of_forall fun x =>
        show x ∈ inner → x ∈ U from fun hx => hinnerU hx)
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
  have hQInt :
      IntegrableOn
        (fun x => w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hG
    simpa only [G, vecNormSq_smul] using hraw
  have hwSqInt : IntegrableOn (fun x => w x ^ 2) U := by
    simpa only [pow_two] using
      integrableOn_mul_of_memL2On hw hw
  have hQrestrict :
      (∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) =
        ∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet houter fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp [vecNormSq, vecDot]
  have hQOuter :
      IntegrableOn
        (fun x => w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) outer :=
    hQInt.mono_set houter
  have hKSqOuter :
      IntegrableOn (fun x => K ^ 2 * w x ^ 2) outer :=
    (hwSqInt.mono_set houter).const_mul (K ^ 2)
  have hQle :
      (∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
        K ^ 2 * ∫ x in outer, w x ^ 2 := by
    calc
      (∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
          ∫ x in outer, K ^ 2 * w x ^ 2 := by
            exact MeasureTheory.setIntegral_mono_on hQOuter hKSqOuter
              houterMeas fun x _hx => by
                have hgradSq :
                    vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
                  calc
                    vecNormSq (classicalGradient η.toFun x) =
                        vecEuclideanNorm
                            (classicalGradient η.toFun x) ^ 2 :=
                      (vecEuclideanNorm_sq _).symm
                    _ ≤ K ^ 2 :=
                      pow_le_pow_left₀
                        (vecEuclideanNorm_nonneg _)
                        (η.gradient_bound x) 2
                calc
                  w x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤
                      w x ^ 2 * K ^ 2 :=
                    mul_le_mul_of_nonneg_left hgradSq (sq_nonneg (w x))
                  _ = K ^ 2 * w x ^ 2 := by ring
      _ = K ^ 2 * ∫ x in outer, w x ^ 2 :=
        MeasureTheory.integral_const_mul (K ^ 2) _
  have hbase :=
    caccioppoli_integrated_positivePart_gradient_of_h10Subharmonic
      (k := k) hU hEll hlam hsub η houter
  have hcoefficient : 0 ≤ 4 * Lam / lam :=
    div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
  change (∫ x in inner, vecNormSq (ξ x)) ≤ _
  calc
    (∫ x in inner, vecNormSq (ξ x)) ≤
        ∫ x in U, η x ^ 2 * vecNormSq (ξ x) :=
      hinnerLe
    _ ≤ (4 * Lam / lam) *
        ∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
      simpa only [w, ξ] using hbase
    _ = (4 * Lam / lam) *
        ∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
      rw [hQrestrict]
    _ ≤ (4 * Lam / lam) *
        (K ^ 2 * ∫ x in outer, w x ^ 2) :=
      mul_le_mul_of_nonneg_left hQle hcoefficient
    _ = (4 * Lam / lam) * K ^ 2 *
        ∫ x in outer, max (u x - k) 0 ^ 2 := by
      simp only [w]
      ring

/-- Homogeneous-solution wrapper for the geometry-free cutoff estimate. -/
theorem caccioppoli_positivePart_on_inner
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hinnerMeas : MeasurableSet inner)
    (houterMeas : MeasurableSet outer)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    ∫ x in inner,
        vecNormSq ({y | k < u y}.indicator u.grad x) ≤
      (4 * Lam / lam) * K ^ 2 * ∫ x in outer,
        max (u x - k) 0 ^ 2 :=
  caccioppoli_positivePart_on_inner_of_h10Subharmonic
    (k := k) hU hinnerMeas houterMeas hEll hlam hLam
      (hsol.toH10SubharmonicOn hEll) η houter

end PDE
