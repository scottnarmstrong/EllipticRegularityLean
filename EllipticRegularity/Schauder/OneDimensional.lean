module

public import PDEFoundation.PDE.OneDimensionalFlux
public import PDEFoundation.PDE.PerturbationL2
public import PDEFoundation.Sobolev.OneDimensional.ForcedHolder
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
public import PDEFoundation.Regularity.Holder

/-! # The one-dimensional small-perturbation Hölder estimate -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- In one dimension, Euclidean magnitude is the sole absolute coordinate. -/
theorem vecEuclideanNorm_one_eq_abs (x : Vec 1) : vecEuclideanNorm x = |x 0| := by
  simp only [vecEuclideanNorm, vecNormSq, vecDot, Fin.sum_univ_one]
  rw [← pow_two, Real.sqrt_sq_eq_abs]

/-- A native round ball on `Vec 1` is exactly the corresponding scalar interval. -/
theorem euclideanBall_zero_one_eq_axisBox {r : ℝ} (hr : 0 < r) :
    euclideanBall (0 : Vec 1) r = oneDimensionalAxisBox (-r) r := by
  ext x
  simp only [euclideanBall, Set.mem_ofPred_eq, euclideanSqDist, vecNormSq, vecDot,
    Pi.sub_apply, Pi.zero_apply, sub_zero, Fin.sum_univ_one,
    mem_oneDimensionalAxisBox_iff, vecOneCoordinate, Set.mem_Ioo]
  constructor
  · intro hx
    constructor <;> nlinarith [sq_nonneg (x 0 + r), sq_nonneg (x 0 - r)]
  · intro hx
    nlinarith [mul_pos (sub_pos.mpr hx.2) (by linarith : 0 < x 0 + r)]

/-- On the interval of length two, the exact Hölder measure factor is at most
 two, uniformly in every exponent greater than one. -/
theorem setIntegral_abs_unitInterval_le_two_eLpNorm
    {f : ℝ → ℝ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1))) :
    (∫ t in Ioo (-1 : ℝ) 1, |f t|) ≤
      2 * (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := by
  have h := integral_abs_le_eLpNorm_mul_measure_rpow hp hf
  have hmeasure : (volume.restrict (Ioo (-1 : ℝ) 1) Set.univ).toReal = 2 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num
  rw [hmeasure] at h
  have he : 1 - 1 / p ≤ 1 := by
    linarith [one_div_pos.mpr (zero_lt_one.trans hp)]
  have hpow : (2 : ℝ) ^ (1 - 1 / p) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  exact h.trans ((mul_le_mul_of_nonneg_left hpow ENNReal.toReal_nonneg).trans_eq
    (mul_comm _ _))

/-- An actual constant flux on the unit interval has a bound uniform in `p`. -/
theorem abs_constantFlux_le_two_norms
    {k g F : ℝ → ℝ} {p c : ℝ} (hp : 1 < p)
    (hg : MemLp g 2 (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hq : IntegrableOn (fun t => k t * g t + F t) (Ioo (-1 : ℝ) 1))
    (hk : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), |k t| ≤ 3 / 2)
    (hc : (fun t => k t * g t + F t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
      fun _ => c) :
    |c| ≤ 2 * ((eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
      (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) := by
  have hgabs : IntegrableOn (fun t => |g t|) (Ioo (-1 : ℝ) 1) := by
    simpa only [Real.norm_eq_abs] using! (hg.integrable (by norm_num)).norm
  have hFabs : IntegrableOn (fun t => |F t|) (Ioo (-1 : ℝ) 1) := by
    simpa only [Real.norm_eq_abs] using! (hF.integrable (ENNReal.one_le_ofReal.mpr hp.le)).norm
  have heq : (∫ t in Ioo (-1 : ℝ) 1, k t * g t + F t) = 2 * c := by
    rw [integral_congr_ae hc, setIntegral_const, measureReal_def, Real.volume_Ioo]
    norm_num [smul_eq_mul]
  have habs : (∫ t in Ioo (-1 : ℝ) 1, |k t * g t + F t|) ≤
      (3 / 2) * (∫ t in Ioo (-1 : ℝ) 1, |g t|) +
        ∫ t in Ioo (-1 : ℝ) 1, |F t| := by
    calc
      _ ≤ ∫ t in Ioo (-1 : ℝ) 1, (3 / 2) * |g t| + |F t| := by
        apply integral_mono_ae hq.norm ((hgabs.const_mul (3 / 2)).add hFabs)
        filter_upwards [hk] with t ht
        exact (abs_add_le _ _).trans
          (add_le_add (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)) le_rfl)
      _ = _ := by rw [integral_add (hgabs.const_mul (3 / 2)) hFabs, integral_const_mul]
  have hnorm : 2 * |c| ≤ (∫ t in Ioo (-1 : ℝ) 1, |k t * g t + F t|) := by
    have h := norm_integral_le_integral_norm (fun t => k t * g t + F t)
      (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    simpa only [Real.norm_eq_abs, heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  have hgint := setIntegral_abs_unitInterval_le_two_eLpNorm (by norm_num : (1 : ℝ) < 2)
    (by simpa only [ENNReal.ofReal_ofNat] using hg)
  simp only [ENNReal.ofReal_ofNat] at hgint
  have hFint := setIntegral_abs_unitInterval_le_two_eLpNorm hp hF
  have hg0 : 0 ≤ (eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hF0 : 0 ≤ (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  linarith

/-- The scalar constant-flux argument gives a uniform inner-interval estimate. -/
theorem exists_holder_representative_of_unitInterval_constantFlux
    {k u g F : ℝ → ℝ} {α p c : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 < p) (hpα : 1 - 1 / p = α)
    (hu : MemLp u 2 (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hweak : HasWeakDerivOnIoo (-1) 1 u g)
    (hF : MemLp F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)))
    (hq : IntegrableOn (fun t => k t * g t + F t) (Ioo (-1 : ℝ) 1))
    (hk : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), 1 / 2 ≤ k t ∧ k t ≤ 3 / 2)
    (hc : (fun t => k t * g t + F t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] fun _ => c) :
    ∃ v : ℝ → ℝ, u =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] v ∧
      ∀ x ∈ Ioo (-1 / 2 : ℝ) (1 / 2), ∀ y ∈ Ioo (-1 / 2 : ℝ) (1 / 2),
        |v x - v y| ≤ 8 *
          ((eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal +
            (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1))).toReal) *
              |x - y| ^ α := by
  have hkab : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), |k t| ≤ 3 / 2 := by
    filter_upwards [hk] with t ht
    rw [abs_of_nonneg (by linarith : 0 ≤ k t)]
    exact ht.2
  have hcBound := abs_constantFlux_le_two_norms hp hg hF hq hkab hc
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1),
      |g t| ≤ 2 * |c| + 2 * |F t| := by
    filter_upwards [hk, hc] with t ht hct
    have hkg : |k t * g t| ≤ |c| + |F t| := by
      have heq : k t * g t = c - F t := by linarith
      rw [heq]
      exact abs_sub c (F t)
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ k t)] at hkg
    nlinarith [abs_nonneg (g t)]
  obtain ⟨v, _, huv, hv⟩ :=
    exists_continuousOn_representative_with_forced_holder_increment (by norm_num)
      hu hg hweak hp hF (by positivity : 0 ≤ 2 * |c|) (by norm_num : (0 : ℝ) ≤ 2) hderiv
  refine ⟨v, huv, ?_⟩
  intro x hx y hy
  have hxclosed : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyclosed : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hdist : |x - y| ≤ 1 := (abs_le).mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hpow : |x - y| ≤ |x - y| ^ α := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hdist hα.le hα1.le
  have hincrement := hv x hxclosed y hyclosed
  rw [hpα] at hincrement
  have hp0 : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have hF0 : 0 ≤ (eLpNorm F (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hg0 : 0 ≤ (eLpNorm g 2 (volume.restrict (Ioo (-1 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hreplace := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * |c|)
  nlinarith

/-- Exact transport of arbitrary almost everywhere properties on one-coordinate
intervals. -/
theorem ae_scalarToVecOne_iff {a b : ℝ} {P : Vec 1 → Prop} :
    (∀ᵐ t ∂volume.restrict (Ioo a b), P (scalarToVecOne t)) ↔
      ∀ᵐ x ∂volume.restrict (oneDimensionalAxisBox a b), P x := by
  have hpres := volumePreserving_vecOneEquivReal.restrict_preimage_emb
    vecOneEquivReal.measurableEmbedding (Ioo a b)
  rw [← hpres.map_eq, vecOneEquivReal.measurableEmbedding.ae_map_iff,
    vecOneEquivReal_preimage_Ioo]
  simp only [vecOneEquivReal_apply, scalarToVecOne_vecOneCoordinate]

/-- The actual native one-dimensional weak equation yields a Hölder
representative on the half ball, uniformly for the full range of exponents. -/
theorem hasEuclideanHolderRepresentativeOn_halfBall_oneDimensional_of_weakSolution
    {a : CoeffField 1} {α p delta : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 < p) (hpα : 1 - 1 / p = α)
    (hdelta : delta ≤ 1 / 2)
    (u : H1Function (euclideanBall (0 : Vec 1) 1)) {F : Vec 1 → Vec 1}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 1) 1),
      IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemLpOn (euclideanBall (0 : Vec 1) 1) (ENNReal.ofReal p) (fun x => F x 0))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 1) 1) u 0 F) :
    HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec 1) (1 / 2)) u.toFun α
      (8 * ((eLpNorm (fun x => u.grad x 0) 2
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
  have hFScalar : MemLp Fs (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply (memLp_liftOneDimensional_iff_memLp_Ioo (-1) 1).mp
    rw [liftOneDimensional_scalarPullbackOne, ← hball]
    exact hF
  have hweak : HasWeakDerivOnIoo (-1) 1 us gs := by
    unfold HasWeakDerivOnIoo
    rw [liftOneDimensional_scalarPullbackOne, liftOneDimensional_scalarPullbackOne, ← hball]
    exact u.hasWeakPartialDerivOn 0
  let : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec 1) 1)) :=
    isFiniteMeasure_volumeOn_euclideanBall _ (by norm_num)
  have hfluxL2 := memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hclose u.gradMemL2
  have hq : IntegrableOn q (euclideanBall (0 : Vec 1) 1) :=
    ((hfluxL2 0).integrable (by norm_num)).add
      (hF.integrable (ENNReal.one_le_ofReal.mpr hp.le))
  have hqScalar : IntegrableOn (fun t => ks t * gs t + Fs t) (Ioo (-1 : ℝ) 1) := by
    apply (integrableOn_axisBox_one_iff_integrableOn_Ioo (-1) 1).mp
    rw [← hball]
    convert hq using 1
    funext x
    simp only [q, ks, gs, Fs, scalarPullbackOne, liftOneDimensional,
      scalarToVecOne_vecOneCoordinate, matVecMul, Fin.sum_univ_one]
  have hcNative := oneDimensional_totalFlux_ae_eq_integralAverage
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec 1) (by norm_num))
    (volume_euclideanBall_pos _ (by norm_num))
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))) hsol hq
  let c := integralAverage (euclideanBall (0 : Vec 1) 1) q
  have hcScalar : (fun t => ks t * gs t + Fs t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] fun _ => c := by
    have hnative : ∀ᵐ x ∂volume.restrict (oneDimensionalAxisBox (-1) 1), q x = c := by
      simpa only [← hball] using! hcNative
    have h := (ae_scalarToVecOne_iff (a := -1) (b := 1) (P := fun x => q x = c)).mpr hnative
    simpa only [q, ks, gs, Fs, scalarPullbackOne, matVecMul, Fin.sum_univ_one] using! h
  have hkNative : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 1) 1),
      1 / 2 ≤ a x 0 0 ∧ a x 0 0 ≤ 3 / 2 := by
    filter_upwards [ae_abs_matrix_sub_identity_entry_le_of_isMatrixPerturbationLE hclose] with x hx
    have h := hx 0 0
    simp only [Matrix.sub_apply, Matrix.one_apply, ite_true] at h
    have hl := neg_le_of_abs_le h
    have hu := le_of_abs_le h
    constructor <;> linarith
  have hkScalar : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1),
      1 / 2 ≤ ks t ∧ ks t ≤ 3 / 2 := by
    have hnative : ∀ᵐ x ∂volume.restrict (oneDimensionalAxisBox (-1) 1),
        1 / 2 ≤ a x 0 0 ∧ a x 0 0 ≤ 3 / 2 := by
      simpa only [← hball] using hkNative
    exact (ae_scalarToVecOne_iff (a := -1) (b := 1)).mpr hnative
  obtain ⟨v, huv, hv⟩ := exists_holder_representative_of_unitInterval_constantFlux
    hα hα1 hp hpα huScalar hgScalar hweak hFScalar hqScalar hkScalar hcScalar
  have hnormg : eLpNorm gs 2 (volume.restrict (Ioo (-1 : ℝ) 1)) =
      eLpNorm (fun x => u.grad x 0) 2 (volumeOn (euclideanBall (0 : Vec 1) 1)) := by
    rw [← eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo (-1) 1,
      liftOneDimensional_scalarPullbackOne, ← hball]
  have hnormF : eLpNorm Fs (ENNReal.ofReal p) (volume.restrict (Ioo (-1 : ℝ) 1)) =
      eLpNorm (fun x => F x 0) (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec 1) 1)) := by
    rw [← eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo (-1) 1,
      liftOneDimensional_scalarPullbackOne, ← hball]
  have hAE : liftOneDimensional v =ᵐ[volumeOn (euclideanBall (0 : Vec 1) 1)] u.toFun := by
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

/-- The one-dimensional raw coordinate `L²` norm is exactly the square root
of native Euclidean energy. -/
theorem eLpNorm_coord_one_two_toReal_eq_sqrt_energy
    {U : Set (Vec 1)} {G : Vec 1 → Vec 1}
    (hG : MemVectorL2On U G) :
    (eLpNorm (fun x => G x 0) 2 (volumeOn U)).toReal =
      Real.sqrt (∫ x in U, vecNormSq (G x)) := by
  rw [(hG 0).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [← one_div, ← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [vecNormSq, vecDot, Fin.sum_univ_one, pow_two]

/-- The native one-dimensional source estimate with explicit raw energy and
forcing norms. The permitted numerical constant is uniform in `α`. -/
theorem schauder_oneDimensional
    {a : CoeffField 1} {α delta : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hdelta : delta ≤ 1 / 2)
    (u : H1Function (euclideanBall (0 : Vec 1) 1)) {F : Vec 1 → Vec 1}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 1) 1),
      IsMatrixPerturbationLE delta (a x) 1)
    (hFmeas : AEStronglyMeasurable (fun x => F x 0)
      (volumeOn (euclideanBall (0 : Vec 1) 1)))
    (hF : MemLpOn (euclideanBall (0 : Vec 1) 1) (ENNReal.ofReal (1 / (1 - α)))
      (fun x => vecEuclideanNorm (F x)))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 1) 1) u 0 F) :
    HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec 1) (1 / 2)) u.toFun α
      (8 * (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1, vecNormSq (u.grad x)) +
        (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
          (ENNReal.ofReal (1 / (1 - α))) F).toReal)) := by
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
  have h := hasEuclideanHolderRepresentativeOn_halfBall_oneDimensional_of_weakSolution
    hα hα1 hp hpα hdelta u ha hclose hFcoord hsol
  have hnormF : eLpNorm (fun x => F x 0) (ENNReal.ofReal (1 / (1 - α)))
      (volumeOn (euclideanBall (0 : Vec 1) 1)) =
      euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal (1 / (1 - α))) F := by
    unfold euclideanFieldELpNormOn eLpNormOn
    simp only [vecEuclideanNorm_one_eq_abs, ← Real.norm_eq_abs]
    exact (eLpNorm_norm (fun x => F x 0) hFmeas).symm
  rw [eLpNorm_coord_one_two_toReal_eq_sqrt_energy u.gradMemL2, hnormF] at h
  exact h

end

end PDE
