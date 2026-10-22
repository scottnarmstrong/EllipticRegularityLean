module

public import EllipticRegularity.Energy.SmartCaccioppoli
public import PDEFoundation.Sobolev.Cutoff.SquareShell

/-!
# Reabsorbed coefficient-energy Caccioppoli estimate

The shell-localized estimate in `SmartCaccioppoli` is the input for the
two-dimensional hole-filling argument.  This file records its complementary
standard form: retain the weighted energy term in Young's inequality and
reabsorb it.  The result controls coefficient energy directly and has the
literal factor `4 * (Lam / lam)`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open MeasureTheory

private theorem vecDot_smul_right_coefficient_energy {d : ℕ}
    (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem vecDot_add_right_coefficient_energy {d : ℕ}
    (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The fully reabsorbed Caccioppoli estimate for coefficient energy.

The coefficient energy is normalized by `lam`, and the right side displays
the exact cutoff constant.  No symmetry of the coefficient field is used. -/
theorem caccioppoli_coefficient_energy_on_inner
    {d : ℕ} {lam Lam K k : ℝ} {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hinnerMeas : MeasurableSet inner)
    (houterMeas : MeasurableSet outer)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K)
    (houter : outer ⊆ U) :
    (∫ x in inner, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      (4 * Lam / lam) * K ^ 2 * ∫ x in outer, (u x - k) ^ 2 := by
  let w : Vec d → ℝ := fun x => u x - k
  let energy : Vec d → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let G : Vec d → Vec d := fun x => w x • classicalGradient η.toFun x
  let crossGrad : Vec d → Vec d := fun x => (2 * η x) • G x
  let weightedGrad : Vec d → Vec d := fun x => η x ^ 2 • u.grad x
  let φ : H10Function U :=
    H1Function.mulCutoffSqSubConstToH10 hU u k η houter
  have hinnerU : inner ⊆ U := η.inner_subset_outer.trans houter
  have hφgrad : φ.toH1Function.grad =
      fun x => weightedGrad x + crossGrad x := by
    rw [show φ = H1Function.mulCutoffSqSubConstToH10 hU u k η houter from rfl,
      H1Function.mulCutoffSqSubConstToH10_grad]
    funext x
    ext i
    simp only [weightedGrad, crossGrad, G, w, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hηTop : MemLpOn U ∞ η.toFun :=
    W1pFunction.cutoff_memLpTop η
  have hηSqTop : MemLpOn U ∞ η.sq.toFun :=
    W1pFunction.cutoff_memLpTop η.sq
  have hDηTop (i : Fin d) :
      MemLpOn U ∞ (fun x => classicalGradient η.toFun x i) :=
    W1pFunction.cutoff_gradient_memLpTop η i
  have hw : MemL2On U w := by
    simpa only [w, H1Function.subConst_apply] using!
      (u.subConst hU k).memL2
  have hweightedGrad : MemVectorL2On U weightedGrad := by
    intro i
    simpa only [weightedGrad, QuantitativeSmoothCutoff.sq_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] using
      (u.gradMemL2 i).fun_mul hηSqTop
  have hG : MemVectorL2On U G := by
    intro i
    simpa only [G, Pi.smul_apply, smul_eq_mul, mul_comm] using
      (hw.fun_mul (hDηTop i))
  have hcrossGrad : MemVectorL2On U crossGrad := by
    intro i
    have hmul : MemL2On U (fun x => η x * G x i) :=
      hηTop.fun_mul (hG i)
    simpa only [crossGrad, Pi.smul_apply, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm] using! hmul.const_smul (2 : ℝ)
  have hflux : MemVectorL2On U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  have hmainInt : IntegrableOn (fun x => η x ^ 2 * energy x) U := by
    have hraw := integrableOn_vecDot_of_memVectorL2On hflux hweightedGrad
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      simp only [weightedGrad, energy]
      rw [vecDot_smul_right_coefficient_energy, vecDot_comm]
  have hcrossInt : IntegrableOn (fun x =>
      2 * η x * w x * vecDot (matVecMul (a x) (u.grad x))
        (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecDot_of_memVectorL2On hflux hcrossGrad
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      simp only [crossGrad, G]
      rw [vecDot_smul_right_coefficient_energy,
        vecDot_smul_right_coefficient_energy]
      ring
  have hwSqInt : IntegrableOn (fun x => w x ^ 2) U := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hw hw
  have henergyNonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ energy x := by
    refine (ae_restrict_iff' hU.measurableSet).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hA := hEll.elliptic hx
    exact (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg (u.grad x))).trans
      (hA.coercive (u.grad x))
  have hinnerWeighted :
      (∫ x in inner, energy x) = ∫ x in inner, η x ^ 2 * energy x := by
    exact setIntegral_congr_fun hinnerMeas fun x hx => by
      rw [η.eq_one_on_inner x hx]
      ring
  have hinnerLeMain : (∫ x in inner, energy x) ≤
      ∫ x in U, η x ^ 2 * energy x := by
    rw [hinnerWeighted]
    exact setIntegral_mono_set hmainInt
      (henergyNonneg.mono fun x hx => mul_nonneg (sq_nonneg (η x)) hx)
      (Filter.Eventually.of_forall fun x hx => hinnerU hx)
  have htest := (hsol.toH10SolutionOn hEll) φ
  have hweak : ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
      (φ.toH1Function.grad x) = 0 := by
    simpa only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
      integral_zero, sub_zero] using htest.2
  have hsum : (∫ x in U, η x ^ 2 * energy x) +
      ∫ x in U, 2 * η x * w x *
        vecDot (matVecMul (a x) (u.grad x))
          (classicalGradient η.toFun x) = 0 := by
    calc
      (∫ x in U, η x ^ 2 * energy x) +
          ∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (u.grad x))
              (classicalGradient η.toFun x) =
          ∫ x in U, (η x ^ 2 * energy x) +
            (2 * η x * w x * vecDot (matVecMul (a x) (u.grad x))
              (classicalGradient η.toFun x)) :=
        (integral_add hmainInt hcrossInt).symm
      _ = ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hφgrad, vecDot_add_right_coefficient_energy]
        simp only [weightedGrad, crossGrad, G, energy]
        simp_rw [vecDot_smul_right_coefficient_energy]
        rw [vecDot_comm (matVecMul (a x) (u.grad x)) (u.grad x)]
        ring
      _ = 0 := hweak
  have hmainLeAbs : (∫ x in U, η x ^ 2 * energy x) ≤
      |∫ x in U, 2 * η x * w x *
        vecDot (matVecMul (a x) (u.grad x))
          (classicalGradient η.toFun x)| := by
    have hneg : (∫ x in U, η x ^ 2 * energy x) =
        -(∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)) := by
      linarith [hsum]
    rw [hneg]
    exact neg_le_abs _
  have hcrossAbsInt : IntegrableOn (fun x => |2 * η x * w x *
      vecDot (matVecMul (a x) (u.grad x))
        (classicalGradient η.toFun x)|) U := hcrossInt.abs
  have hhalfInt : IntegrableOn (fun x =>
      (η x ^ 2 * energy x) / 2) U := hmainInt.div_const 2
  have herrorInt : IntegrableOn (fun x =>
      2 * Lam * w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) U := by
    have hraw := integrableOn_vecNormSq_of_memVectorL2On hG
    have hrewrite : (fun x => 2 * Lam * vecNormSq (G x)) =
        fun x => 2 * Lam * w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
      funext x
      simp only [G, vecNormSq_smul]
      ring
    rw [← hrewrite]
    exact hraw.const_mul (2 * Lam)
  have hpointwise : ∀ᵐ x ∂volumeOn U,
      |2 * η x * w x * vecDot (matVecMul (a x) (u.grad x))
        (classicalGradient η.toFun x)| ≤
        (η x ^ 2 * energy x) / 2 +
          2 * Lam * w x ^ 2 * vecNormSq (classicalGradient η.toFun x) := by
    refine (ae_restrict_iff' hU.measurableSet).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hA := hEll.elliptic hx
    have hbase := abs_two_mul_mul_vecDot_matVecMul_le_caccioppoli hA
      (u.grad x) (classicalGradient η.toFun x) (eta := η x) (w := w x)
    calc
      |2 * η x * w x * vecDot (matVecMul (a x) (u.grad x))
          (classicalGradient η.toFun x)| ≤
          (η x ^ 2 * energy x) / 2 +
            2 * Lam * w x ^ 2 * vecNormSq (classicalGradient η.toFun x) := by
        simpa only [energy] using hbase
      _ = (η x ^ 2 * energy x) / 2 +
          2 * Lam * w x ^ 2 * vecNormSq (classicalGradient η.toFun x) := rfl
  have hboundInt : IntegrableOn (fun x =>
      (η x ^ 2 * energy x) / 2 +
        2 * Lam * w x ^ 2 * vecNormSq (classicalGradient η.toFun x)) U :=
    hhalfInt.add herrorInt
  have hbound := integral_mono_ae hcrossAbsInt hboundInt hpointwise
  have habsIntegral : |∫ x in U, 2 * η x * w x *
      vecDot (matVecMul (a x) (u.grad x))
        (classicalGradient η.toFun x)| ≤
      ∫ x in U, |2 * η x * w x *
        vecDot (matVecMul (a x) (u.grad x))
          (classicalGradient η.toFun x)| := abs_integral_le_integral_abs
  have hmainLe : (∫ x in U, η x ^ 2 * energy x) ≤
      (∫ x in U, η x ^ 2 * energy x) / 2 +
        ∫ x in U, 2 * Lam * w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
    calc
      (∫ x in U, η x ^ 2 * energy x) ≤
          |∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (u.grad x))
              (classicalGradient η.toFun x)| := hmainLeAbs
      _ ≤ ∫ x in U, |2 * η x * w x *
            vecDot (matVecMul (a x) (u.grad x))
              (classicalGradient η.toFun x)| := habsIntegral
      _ ≤ ∫ x in U, (η x ^ 2 * energy x) / 2 +
            2 * Lam * w x ^ 2 *
              vecNormSq (classicalGradient η.toFun x) := hbound
      _ = (∫ x in U, η x ^ 2 * energy x) / 2 +
          ∫ x in U, 2 * Lam * w x ^ 2 *
            vecNormSq (classicalGradient η.toFun x) := by
        rw [integral_add hhalfInt herrorInt, integral_div]
  have hweighted : (∫ x in U, η x ^ 2 * energy x) ≤
      4 * Lam * ∫ x in U, w x ^ 2 *
        vecNormSq (classicalGradient η.toFun x) := by
    have herrorEq :
        (∫ x in U, 2 * Lam * w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) =
        (2 * Lam) * ∫ x in U, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x) := by
      simpa only [mul_assoc] using
        (integral_const_mul (2 * Lam)
          (fun x => w x ^ 2 * vecNormSq (classicalGradient η.toFun x)))
    rw [herrorEq] at hmainLe
    nlinarith
  have hqRestrict : (∫ x in U, w x ^ 2 *
      vecNormSq (classicalGradient η.toFun x)) =
      ∫ x in outer, w x ^ 2 *
        vecNormSq (classicalGradient η.toFun x) := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet houter fun x hx => by
        rw [η.classicalGradient_eq_zero_of_not_mem_outer hx.2]
        simp [vecNormSq, vecDot]
  have hqOuter : IntegrableOn (fun x => w x ^ 2 *
      vecNormSq (classicalGradient η.toFun x)) outer :=
    have hqU : IntegrableOn (fun x => w x ^ 2 *
        vecNormSq (classicalGradient η.toFun x)) U := by
      have hraw := integrableOn_vecNormSq_of_memVectorL2On hG
      simpa only [G, vecNormSq_smul] using hraw
    hqU.mono_set houter
  have hKSqOuter : IntegrableOn (fun x => K ^ 2 * w x ^ 2) outer :=
    (hwSqInt.mono_set houter).const_mul (K ^ 2)
  have hqLe : (∫ x in outer, w x ^ 2 *
      vecNormSq (classicalGradient η.toFun x)) ≤
      K ^ 2 * ∫ x in outer, w x ^ 2 := by
    calc
      (∫ x in outer, w x ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) ≤
          ∫ x in outer, K ^ 2 * w x ^ 2 := by
        exact setIntegral_mono_on hqOuter hKSqOuter houterMeas fun x _hx => by
          have hgradSq : vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
            calc
              vecNormSq (classicalGradient η.toFun x) =
                  vecEuclideanNorm (classicalGradient η.toFun x) ^ 2 :=
                (vecEuclideanNorm_sq _).symm
              _ ≤ K ^ 2 := pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
                (η.gradient_bound x) 2
          calc
            w x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤
                w x ^ 2 * K ^ 2 :=
              mul_le_mul_of_nonneg_left hgradSq (sq_nonneg (w x))
            _ = K ^ 2 * w x ^ 2 := by ring
      _ = K ^ 2 * ∫ x in outer, w x ^ 2 :=
        integral_const_mul (K ^ 2) _
  have hcoefficient : 0 ≤ 4 * Lam / lam :=
    div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
  calc
    (∫ x in inner, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam =
        (1 / lam) * ∫ x in inner, energy x := by ring
    _ ≤ (1 / lam) * ∫ x in U, η x ^ 2 * energy x :=
      mul_le_mul_of_nonneg_left hinnerLeMain (one_div_nonneg.mpr hlam.le)
    _ ≤ (1 / lam) * (4 * Lam * ∫ x in U, w x ^ 2 *
        vecNormSq (classicalGradient η.toFun x)) :=
      mul_le_mul_of_nonneg_left hweighted (one_div_nonneg.mpr hlam.le)
    _ = (4 * Lam / lam) * ∫ x in outer, w x ^ 2 *
        vecNormSq (classicalGradient η.toFun x) := by rw [hqRestrict]; ring
    _ ≤ (4 * Lam / lam) * (K ^ 2 * ∫ x in outer, w x ^ 2) :=
      mul_le_mul_of_nonneg_left hqLe hcoefficient
    _ = (4 * Lam / lam) * K ^ 2 * ∫ x in outer, (u x - k) ^ 2 := by
      simp only [w]
      ring

/-- The reabsorbed coefficient-energy estimate on a centered square.

Here the cutoff has Euclidean gradient bound `64 / r`; consequently the
coefficient is exactly `4 * 64^2 = 16384`.  The expression `... / r^2`
is the displayed scale factor `r⁻²`. -/
theorem caccioppoli_coefficient_energy_on_centeredSquare
    {lam Lam k : ℝ} {U : Set (Vec 2)}
    {a : CoeffField 2} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U) (x₀ : Vec 2) {r : ℝ}
    (hr : 0 < r) (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    (∫ x in closedCenteredAxisCube x₀ r,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      (16384 * (Lam / lam) / r ^ 2) *
        ∫ x in centeredAxisCube x₀ (2 * r), (u x - k) ^ 2 := by
  have hbase := caccioppoli_coefficient_energy_on_inner
    hU (isClosed_closedCenteredAxisCube x₀ r).measurableSet
      (isOpen_centeredAxisCube x₀ (2 * r)).measurableSet
      hEll hlam hLam hsol (quantitativeSquareShellCutoff x₀ hr) houter
      (k := k)
  convert hbase using 1
  field_simp [hr.ne']
  ring

end PDE
