module

public import EllipticRegularity.Energy.CaccioppoliPointwise
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

@[expose] public section

open scoped ENNReal Topology

/-!
# Smart Caccioppoli estimate for hole filling

For a harmonic function, the untruncated test `η² (u-k)` permits a
nonabsorbing Young parameter. Localizing the cross term to the transition
shell before applying Young's inequality gives

`energy(inner) ≤ τ energy(shell) + (Λ / τ) K² oscillation(shell)`.

The parameter remains explicit. The later sharp choice
`τ = sqrt (Λ / λ)` therefore produces square-root ellipticity-ratio
dependence after normalizing the energy by `λ`.
-/

namespace PDE

open MeasureTheory

private theorem vecDot_smul_right_smart {d : ℕ}
    (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem vecDot_add_right_smart {d : ℕ}
    (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The parameterized, shell-localized Caccioppoli estimate for a homogeneous
weak solution.

The shell is literally `outer \ inner`. The first term is coefficient energy,
not merely Euclidean gradient energy, and all dependence on `τ`, `Λ`, and the
cutoff-gradient bound `K` is displayed. No symmetry of the coefficient field
is assumed. -/
theorem smart_caccioppoli_energy_on_inner
    {d : ℕ} {lam Lam K k tau : ℝ}
    {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hinnerMeas : MeasurableSet inner)
    (houterMeas : MeasurableSet outer)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hLam : 0 ≤ Lam) (htau : 0 < tau)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K)
    (houter : outer ⊆ U) :
    ∫ x in inner, vecDot (u.grad x) (matVecMul (a x) (u.grad x)) ≤
      tau * (∫ x in outer \ inner,
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
      (Lam / tau) * K ^ 2 *
        (∫ x in outer \ inner, (u x - k) ^ 2) := by
  let shell : Set (Vec d) := outer \ inner
  let w : Vec d → ℝ := fun x => u x - k
  let energy : Vec d → ℝ :=
    fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))
  let G : Vec d → Vec d :=
    fun x => w x • classicalGradient η.toFun x
  let crossGrad : Vec d → Vec d := fun x => (2 * η x) • G x
  let weightedGrad : Vec d → Vec d := fun x => η x ^ 2 • u.grad x
  let φ : H10Function U :=
    H1Function.mulCutoffSqSubConstToH10 hU u k η houter
  have hshellMeas : MeasurableSet shell := by
    exact houterMeas.diff hinnerMeas
  have hshellU : shell ⊆ U := by
    intro x hx
    exact houter hx.1
  have hinnerU : inner ⊆ U :=
    η.inner_subset_outer.trans houter
  have hφgrad :
      φ.toH1Function.grad =
        fun x => weightedGrad x + crossGrad x := by
    rw [show φ =
        H1Function.mulCutoffSqSubConstToH10 hU u k η houter from rfl,
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
    have hmul :
        MemL2On U (fun x => η x * G x i) :=
      hηTop.fun_mul (hG i)
    simpa only [crossGrad, Pi.smul_apply, smul_eq_mul, mul_assoc,
      mul_left_comm, mul_comm] using! hmul.const_smul (2 : ℝ)
  have hflux :
      MemVectorL2On U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2On_matVecMul_of_isEllipticFieldOn hEll u.gradMemL2
  have henergyInt : IntegrableOn energy U := by
    have hraw :=
      integrableOn_vecDot_of_memVectorL2On hflux u.gradMemL2
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      simp only [energy]
      exact vecDot_comm _ _
  have hmainInt :
      IntegrableOn
        (fun x => η x ^ 2 * energy x) U := by
    have hraw :=
      integrableOn_vecDot_of_memVectorL2On hflux hweightedGrad
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      simp only [weightedGrad, energy]
      rw [vecDot_smul_right_smart, vecDot_comm]
  have hcrossInt :
      IntegrableOn
        (fun x => 2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)) U := by
    have hraw :=
      integrableOn_vecDot_of_memVectorL2On hflux hcrossGrad
    refine (integrableOn_congr_fun_ae ?_).mp hraw
    exact Filter.Eventually.of_forall fun x => by
      simp only [crossGrad, G]
      rw [vecDot_smul_right_smart, vecDot_smul_right_smart]
      ring
  have hwSqInt : IntegrableOn (fun x => w x ^ 2) U := by
    simpa only [pow_two] using
      integrableOn_mul_of_memL2On hw hw
  have henergyNonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ energy x := by
    refine (ae_restrict_iff' hU.measurableSet).2 ?_
    exact Filter.Eventually.of_forall fun x hx => by
      have hA := hEll.elliptic hx
      exact
        (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg (u.grad x))).trans
          (hA.coercive (u.grad x))
  have hinnerWeighted :
      (∫ x in inner, energy x) =
        ∫ x in inner, η x ^ 2 * energy x := by
    exact setIntegral_congr_fun hinnerMeas fun x hx => by
      rw [η.eq_one_on_inner x hx]
      ring
  have hinnerLeMain :
      (∫ x in inner, energy x) ≤
        ∫ x in U, η x ^ 2 * energy x := by
    rw [hinnerWeighted]
    exact setIntegral_mono_set hmainInt
      (henergyNonneg.mono fun x hx =>
        mul_nonneg (sq_nonneg (η x)) hx)
      (Filter.Eventually.of_forall fun x =>
        show x ∈ inner → x ∈ U from fun hx => hinnerU hx)
  have htest :=
    (hsol.toH10SolutionOn hEll) φ
  have hweak :
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) = 0 := by
    simpa only [Pi.zero_apply, zero_mul, vecDot, Finset.sum_const_zero,
      integral_zero, sub_zero] using htest.2
  have hsum :
      (∫ x in U, η x ^ 2 * energy x) +
        ∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x) = 0 := by
    calc
      (∫ x in U, η x ^ 2 * energy x) +
          ∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (u.grad x))
              (classicalGradient η.toFun x) =
          ∫ x in U,
            (η x ^ 2 * energy x) +
              (2 * η x * w x *
                vecDot (matVecMul (a x) (u.grad x))
                  (classicalGradient η.toFun x)) :=
        (integral_add hmainInt hcrossInt).symm
      _ = ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (φ.toH1Function.grad x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hφgrad, vecDot_add_right_smart]
        simp only [weightedGrad, crossGrad, G, energy]
        simp_rw [vecDot_smul_right_smart]
        rw [
          vecDot_comm (matVecMul (a x) (u.grad x)) (u.grad x)]
        ring
      _ = 0 := hweak
  have hmainLeAbs :
      (∫ x in U, η x ^ 2 * energy x) ≤
        |∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| := by
    have hneg :
        (∫ x in U, η x ^ 2 * energy x) =
          -(∫ x in U, 2 * η x * w x *
            vecDot (matVecMul (a x) (u.grad x))
              (classicalGradient η.toFun x)) := by
      linarith [hsum]
    rw [hneg]
    exact neg_le_abs _
  have habsIntegral :
      |∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| ≤
        ∫ x in U, |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| :=
    abs_integral_le_integral_abs
  have hcrossAbsRestrict :
      (∫ x in U, |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)|) =
        ∫ x in shell, |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hU.measurableSet hshellU fun x hx => by
        have hgradZero : classicalGradient η.toFun x = 0 := by
          by_cases hxinner : x ∈ inner
          · exact η.classicalGradient_eq_zero_of_mem_inner hxinner
          · apply η.classicalGradient_eq_zero_of_not_mem_outer
            intro hxouter
            exact hx.2 ⟨hxouter, hxinner⟩
        rw [hgradZero]
        simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          abs_zero]
  have hcrossAbsShell :
      IntegrableOn
        (fun x => |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)|) shell :=
    (hcrossInt.mono_set hshellU).abs
  have henergyShell : IntegrableOn energy shell :=
    henergyInt.mono_set hshellU
  have hwSqShell : IntegrableOn (fun x => w x ^ 2) shell :=
    hwSqInt.mono_set hshellU
  have henergyTerm :
      IntegrableOn (fun x => tau * energy x) shell :=
    henergyShell.const_mul tau
  have hvalueTerm :
      IntegrableOn
        (fun x => ((Lam / tau) * K ^ 2) * w x ^ 2) shell :=
    hwSqShell.const_mul ((Lam / tau) * K ^ 2)
  have hpointwise : ∀ x ∈ shell,
      |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| ≤
        tau * energy x + ((Lam / tau) * K ^ 2) * w x ^ 2 := by
    intro x hx
    have hxU : x ∈ U := hshellU hx
    have hA := hEll.elliptic hxU
    have henergyX : 0 ≤ energy x := by
      exact
        (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg (u.grad x))).trans
          (hA.coercive (u.grad x))
    have hηSq : η x ^ 2 ≤ 1 := by
      exact (sq_le_one_iff₀ (η.nonneg x)).2 (η.le_one x)
    have hweightedEnergy :
        tau * (η x ^ 2 * energy x) ≤ tau * energy x := by
      apply mul_le_mul_of_nonneg_left _ htau.le
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hηSq henergyX
    have hgradSq :
        vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
      calc
        vecNormSq (classicalGradient η.toFun x) =
            vecEuclideanNorm (classicalGradient η.toFun x) ^ 2 :=
          (vecEuclideanNorm_sq _).symm
        _ ≤ K ^ 2 :=
          pow_le_pow_left₀ (vecEuclideanNorm_nonneg _)
            (η.gradient_bound x) 2
    have hcutoffError :
        (Lam / tau) * w x ^ 2 *
            vecNormSq (classicalGradient η.toFun x) ≤
          ((Lam / tau) * K ^ 2) * w x ^ 2 := by
      have hcoefficient :
          0 ≤ (Lam / tau) * w x ^ 2 :=
        mul_nonneg (div_nonneg hLam htau.le) (sq_nonneg (w x))
      calc
        (Lam / tau) * w x ^ 2 *
            vecNormSq (classicalGradient η.toFun x) ≤
          (Lam / tau) * w x ^ 2 * K ^ 2 :=
            mul_le_mul_of_nonneg_left hgradSq hcoefficient
        _ = ((Lam / tau) * K ^ 2) * w x ^ 2 := by ring
    exact
      (abs_two_mul_mul_vecDot_matVecMul_le_caccioppoli_parameter
        hA htau (u.grad x) (classicalGradient η.toFun x)
        (eta := η x) (w := w x)).trans
        (add_le_add hweightedEnergy hcutoffError)
  have hbound :
      (∫ x in shell, |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)|) ≤
        ∫ x in shell,
          tau * energy x + ((Lam / tau) * K ^ 2) * w x ^ 2 :=
    setIntegral_mono_on hcrossAbsShell
      (henergyTerm.add hvalueTerm) hshellMeas hpointwise
  calc
    (∫ x in inner, vecDot (u.grad x)
        (matVecMul (a x) (u.grad x))) =
        ∫ x in inner, energy x := by rfl
    _ ≤ ∫ x in U, η x ^ 2 * energy x :=
      hinnerLeMain
    _ ≤ |∫ x in U, 2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| :=
      hmainLeAbs
    _ ≤ ∫ x in U, |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| :=
      habsIntegral
    _ = ∫ x in shell, |2 * η x * w x *
          vecDot (matVecMul (a x) (u.grad x))
            (classicalGradient η.toFun x)| :=
      hcrossAbsRestrict
    _ ≤ ∫ x in shell,
        tau * energy x + ((Lam / tau) * K ^ 2) * w x ^ 2 :=
      hbound
    _ = tau * (∫ x in shell, energy x) +
        ((Lam / tau) * K ^ 2) * (∫ x in shell, w x ^ 2) := by
      rw [integral_add henergyTerm hvalueTerm,
        integral_const_mul, integral_const_mul]
    _ = tau * (∫ x in outer \ inner,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
        (Lam / tau) * K ^ 2 *
          (∫ x in outer \ inner, (u x - k) ^ 2) := by
      rfl

/-- Exact arithmetic behind the smart choice
`τ = sqrt (Λ / λ)`. -/
theorem Lam_div_sqrt_ratio_div_lam_eq_sqrt_ratio
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam) :
    (Lam / Real.sqrt (Lam / lam)) / lam =
      Real.sqrt (Lam / lam) := by
  have hratio : 0 < Lam / lam :=
    div_pos hLam hlam
  have hsqrt : 0 < Real.sqrt (Lam / lam) :=
    Real.sqrt_pos.2 hratio
  field_simp [hsqrt.ne', hlam.ne']
  rw [Real.sq_sqrt hratio.le]
  field_simp [hlam.ne']

/-- The smart Caccioppoli estimate with coefficient energy normalized by
`λ` and the sharp parameter `sqrt (Λ / λ)` substituted literally.

Both the shell energy and the shell oscillation carry exactly one factor
`sqrt (Λ / λ)`. This is the form used before annular Poincaré and
hole filling. -/
theorem smart_caccioppoli_normalized_energy_sqrt_on_inner
    {d : ℕ} {lam Lam K k : ℝ}
    {U inner outer : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hinnerMeas : MeasurableSet inner)
    (houterMeas : MeasurableSet outer)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (η : QuantitativeSmoothCutoff inner outer K)
    (houter : outer ⊆ U) :
    (∫ x in inner,
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam ≤
      Real.sqrt (Lam / lam) *
        ((∫ x in outer \ inner,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) +
      Real.sqrt (Lam / lam) * K ^ 2 *
        (∫ x in outer \ inner, (u x - k) ^ 2) := by
  let sqrtRatio : ℝ := Real.sqrt (Lam / lam)
  have hsqrt : 0 < sqrtRatio := by
    exact Real.sqrt_pos.2 (div_pos hLam hlam)
  have hbase :=
    smart_caccioppoli_energy_on_inner
      hU hinnerMeas houterMeas hEll hLam.le hsqrt hsol η houter
      (k := k) (tau := sqrtRatio)
  have hscaled :=
    mul_le_mul_of_nonneg_left hbase (one_div_nonneg.mpr hlam.le)
  have hcoefficient :
      (Lam / sqrtRatio) / lam = sqrtRatio := by
    simpa only [sqrtRatio] using
      Lam_div_sqrt_ratio_div_lam_eq_sqrt_ratio hlam hLam
  calc
    (∫ x in inner,
        vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam =
        (1 / lam) * ∫ x in inner,
          vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
      ring
    _ ≤ (1 / lam) *
        (sqrtRatio *
            (∫ x in outer \ inner,
              vecDot (u.grad x) (matVecMul (a x) (u.grad x))) +
          (Lam / sqrtRatio) * K ^ 2 *
            (∫ x in outer \ inner, (u x - k) ^ 2)) :=
      hscaled
    _ = sqrtRatio *
          ((∫ x in outer \ inner,
            vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) +
        ((Lam / sqrtRatio) / lam) * K ^ 2 *
          (∫ x in outer \ inner, (u x - k) ^ 2) := by
      ring
    _ = Real.sqrt (Lam / lam) *
          ((∫ x in outer \ inner,
            vecDot (u.grad x) (matVecMul (a x) (u.grad x))) / lam) +
        Real.sqrt (Lam / lam) * K ^ 2 *
          (∫ x in outer \ inner, (u x - k) ^ 2) := by
      rw [hcoefficient]

end PDE
