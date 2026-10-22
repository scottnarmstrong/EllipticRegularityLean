module

public import EllipticRegularity.Ch4.GreenFunction.Approx
public import PDEFoundation.Sobolev.Ch4.H10
public import PDEFoundation.Sobolev.Ch4.Cutoff
public import PDEFoundation.PDE.Ch4.Absorb
public import PDEFoundation.PDE.Ch4.CaccioppoliEnergy

/-!
# Caccioppoli bound for the approximate Green functions (Step 6 of Proposition 4.40)

Testing the equation of `Gₙ` with `η(η Gₙ) ∈ H¹₀(B_R)`, where `η` vanishes on `B_{ε/2}` and equals
`1` outside `B_ε`, gives `∫ η² ∇Gₙ·a∇Gₙ ≤ 4Λ ∫ Gₙ² |∇η|²` once `ρₙ ≤ ε/2`; hence the gradients of
`Gₙ` are bounded in `L²(B_R \ B̄_ε)` uniformly in `n`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The Lipschitz cutoff `η_ε = 1 - radialCutoff 0 (ε/2) ε`: `0` on `B̄_{ε/2}`, `1` outside
`B_ε`. -/
noncomputable def outerCutoff (ε : ℝ) : Vec d → ℝ := fun x =>
  1 - Ch4Infra.radialCutoff 0 (ε / 2) ε x

theorem outerCutoff_eucLip {ε : ℝ} (hε : 0 < ε) :
    Ch4Infra.EucLip (2 / ε) (outerCutoff (d := d) ε) := by
  have h := (Ch4Infra.EucLip.const (d := d) (1 : ℝ)).sub
    (Ch4Infra.radialCutoff_eucLip (0 : Vec d) (show ε / 2 < ε by linarith))
  refine h.mono (le_of_eq ?_)
  field_simp
  ring

theorem abs_outerCutoff_le_one (ε : ℝ) (x : Vec d) : |outerCutoff ε x| ≤ 1 := by
  unfold outerCutoff
  have h0 := Ch4Infra.radialCutoff_nonneg (0 : Vec d) (ε / 2) ε x
  have h1 := Ch4Infra.radialCutoff_le_one (0 : Vec d) (ε / 2) ε x
  rw [abs_le]
  constructor <;> linarith

theorem outerCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {x : Vec d}
    (hx : vecEuclideanNorm x ≤ ε / 2) : outerCutoff ε x = 0 := by
  unfold outerCutoff
  rw [Ch4Infra.radialCutoff_eq_one (by linarith) (by rwa [sub_zero]), sub_self]

theorem outerCutoff_eq_one {ε : ℝ} (hε : 0 < ε) {x : Vec d}
    (hx : ε ≤ vecEuclideanNorm x) : outerCutoff ε x = 1 := by
  unfold outerCutoff
  rw [Ch4Infra.radialCutoff_eq_zero (by linarith) (by rwa [sub_zero]), sub_zero]

theorem classicalGradient_outerCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {x : Vec d}
    (hx : vecEuclideanNorm x < ε / 2) : classicalGradient (outerCutoff ε) x = 0 := by
  have hev : outerCutoff (d := d) ε =ᶠ[𝓝 x] fun _ => 0 := by
    have hopen : IsOpen (euclideanBall (0 : Vec d) (ε / 2)) := isOpen_euclideanBall _ _
    have hmem : x ∈ euclideanBall (0 : Vec d) (ε / 2) := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero]; exact hx
    filter_upwards [hopen.mem_nhds hmem] with y hy
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero] at hy
    exact outerCutoff_eq_zero hε hy.le
  funext i
  simp [classicalGradient, hev.fderiv_eq]

theorem vecNormSq_classicalGradient_outerCutoff_le {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    vecNormSq (classicalGradient (outerCutoff ε) x) ≤ (2 / ε) ^ 2 := by
  have h := (outerCutoff_eucLip (d := d) hε).vecEuclideanNorm_classicalGradient_le'
    (by positivity) x
  rw [← vecEuclideanNorm_sq]
  exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) h 2

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Caccioppoli inequality** for `Gₙ` with the cutoff `η_ε` (4.138, `k = 0`). -/
theorem caccioppoli (S : ApproxSetting d Λ R a) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (hn : approxRadius R n ≤ ε / 2) :
    ∫ x in euclideanBall (0 : Vec d) R, outerCutoff ε x ^ 2 *
        vecDot ((S.G n).toH1Function.grad x) (matVecMul (a x) ((S.G n).toH1Function.grad x)) ≤
      2 ^ 2 * Λ / 1 ^ 2 * ∫ x in euclideanBall (0 : Vec d) R,
        (S.G n).toH1Function.toFun x ^ 2 * vecNormSq (classicalGradient (outerCutoff ε) x) := by
  have hB : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall _ _
  have hη := outerCutoff_eucLip (d := d) hε
  have hL : (0 : ℝ) ≤ 2 / ε := by positivity
  have hM := abs_outerCutoff_le_one (d := d) ε
  have hηc : Continuous (outerCutoff (d := d) ε) := hη.continuous hL
  set φ := Ch4Infra.mulLipOfH10 hB (Ch4Infra.mulLipOfH10 hB (S.G n) hη hL hM) hη hL hM
  obtain ⟨htest, heq⟩ := S.solG n φ
  -- the source term vanishes
  have hsrc : ∫ x in (euclideanBall (0 : Vec d) R), approxSource d (approxRadius R n) x *
      φ.toH1Function.toFun x = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ euclideanBall (0 : Vec d) (approxRadius R n)
    · have hx' : vecEuclideanNorm x ≤ ε / 2 := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (approxRadius_pos S.hR n), sub_zero] at hx
        linarith
      change approxSource d (approxRadius R n) x *
        (outerCutoff ε x * (outerCutoff ε x * (S.G n).toH1Function.toFun x)) = 0
      simp [outerCutoff_eq_zero hε hx']
    · simp [approxSource_eq_zero_of_notMem hx]
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at heq
  rw [hsrc] at heq
  have hgrad : ∀ x, vecDot (matVecMul (a x) ((S.G n).toH1Function.grad x)) (φ.toH1Function.grad x) =
      outerCutoff ε x ^ 2 * vecDot ((S.G n).toH1Function.grad x) (matVecMul (a x) ((S.G
          n).toH1Function.grad x)) +
        2 * (outerCutoff ε x * (S.G n).toH1Function.toFun x *
          vecDot (matVecMul (a x) ((S.G n).toH1Function.grad x)) (classicalGradient (outerCutoff ε)
              x)) := by
    intro x
    change vecDot (matVecMul (a x) ((S.G n).toH1Function.grad x))
      (outerCutoff ε x • (outerCutoff ε x • (S.G n).toH1Function.grad x + (S.G n).toH1Function.toFun
          x • classicalGradient
        (outerCutoff ε) x) + (outerCutoff ε x * (S.G n).toH1Function.toFun x) • classicalGradient
          (outerCutoff ε) x) = _
    simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- integrability of the two parts (as in `absorb_open`)
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hB.measurableSet S.hmeas S.hell
    (S.G n).toH1Function.gradMemL2
  have hE : IntegrableOn
      (fun x => outerCutoff ε x ^ 2 * vecDot ((S.G n).toH1Function.grad x) (matVecMul (a x) ((S.G
          n).toH1Function.grad x))) (euclideanBall (0 : Vec d) R) := by
    have hC : MemVectorL2On (euclideanBall (0 : Vec d) R) (fun x => outerCutoff ε x ^ 2 • (S.G
        n).toH1Function.grad x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using
        Ch4Infra.memL2On_mul_bounded ((S.G n).toH1Function.gradMemL2 i) (by fun_prop : Continuous
          fun x => outerCutoff (d := d) ε x ^ 2) (Ch4Infra.abs_sq_le hM)
    simpa only [DGNM.vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  have hωη : MemVectorL2On (euclideanBall (0 : Vec d) R) (fun x => (S.G n).toH1Function.toFun x •
      classicalGradient (outerCutoff ε) x) :=
    fun i => by
      simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
        Ch4Infra.memL2On_mul_partialDeriv hη hL (S.G n).toH1Function.memL2 i
  have hX : IntegrableOn (fun x => outerCutoff ε x * (S.G n).toH1Function.toFun x *
      vecDot (matVecMul (a x) ((S.G n).toH1Function.grad x)) (classicalGradient (outerCutoff ε) x))
          (euclideanBall (0 : Vec d) R) := by
    have hG : MemVectorL2On (euclideanBall (0 : Vec d) R) (fun x => outerCutoff ε x •
        ((S.G n).toH1Function.toFun x • classicalGradient (outerCutoff ε) x)) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using
        Ch4Infra.memL2On_mul_bounded (hωη i) hηc hM
    have := integrableOn_vecDot_of_memVectorL2On hF hG
    refine this.congr_fun (fun x _ => ?_) hB.measurableSet
    simp only [DGNM.vecDot_smul_right]
    ring
  simp_rw [hgrad] at heq
  rw [integral_add hE (hX.const_mul 2), integral_const_mul] at heq
  exact Ch4Infra.absorb_open hB.measurableSet S.hmeas S.hell (S.G n).toH1Function.gradMemL2 hηc hM
      hωη
    (c₁ := 1) (c₂ := 2) one_pos (by rw [one_mul, heq])

/-- **Uniform gradient bound** away from the pole: for `ρₙ ≤ ε/4`,
`∫_{B_R \ B̄_ε} |∇Gₙ|² ≤ 4Λ (2/ε)² K_{ε/2}²`. -/
theorem integral_vecNormSq_grad_le (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ R → ∀ n, approxRadius R n ≤ ε / 4 →
      ∫ x in euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε,
          vecNormSq ((S.G n).toH1Function.grad x) ≤
        4 * Λ * (2 / ε) ^ 2 * poleConst C Λ (ε / 2) S.E d ^ 2 := by
  obtain ⟨C, hC, hL2⟩ := S.eLpNorm_G_le hd
  refine ⟨C, hC, ?_⟩
  intro ε hε hεR n hn
  have hΛ : 1 ≤ Λ := S.one_le_Lam
  set B := euclideanBall (0 : Vec d) R
  have hBm : MeasurableSet B := measurableSet_euclideanBall _ _
  set U := B \ euclideanClosedBall (0 : Vec d) ε
  have hUm : MeasurableSet U := hBm.diff (measurableSet_euclideanClosedBall _ _)
  have hUB : U ⊆ B := Set.sdiff_subset
  set ξ := (S.G n).toH1Function.grad
  set w := (S.G n).toH1Function.toFun
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hBm S.hmeas S.hell
    (S.G n).toH1Function.gradMemL2
  have hηc : Continuous (outerCutoff (d := d) ε) :=
    (outerCutoff_eucLip hε).continuous (by positivity)
  have hE : IntegrableOn
      (fun x => outerCutoff ε x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x))) B := by
    have hC' : MemVectorL2On B (fun x => outerCutoff ε x ^ 2 • ξ x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using
        Ch4Infra.memL2On_mul_bounded ((S.G n).toH1Function.gradMemL2 i)
          (by fun_prop : Continuous fun x => outerCutoff (d := d) ε x ^ 2)
          (Ch4Infra.abs_sq_le (abs_outerCutoff_le_one ε))
    simpa only [DGNM.vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC' hF
  have hnonneg : ∀ x ∈ B, 0 ≤ outerCutoff ε x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) :=
    fun x hx => mul_nonneg (sq_nonneg _) (DGNM.vecDot_matVecMul_self_nonneg (S.hell x hx) _)
  have h1 : ∫ x in U, vecNormSq (ξ x) ≤
      ∫ x in B, outerCutoff ε x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
    calc ∫ x in U, vecNormSq (ξ x)
        ≤ ∫ x in U, outerCutoff ε x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := by
          refine setIntegral_mono_on
            ((integrableOn_vecNormSq_of_memVectorL2On (S.G n).toH1Function.gradMemL2).mono_set
              hUB) (hE.mono_set hUB) hUm fun x hx => ?_
          have hxn : ε ≤ vecEuclideanNorm x := by
            by_contra h
            exact hx.2 ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le hε.le).2
              (by rw [sub_zero]; linarith))
          rw [outerCutoff_eq_one hε hxn, one_pow, one_mul]
          have := (S.hell x (hUB hx)).coercive (ξ x)
          linarith
      _ ≤ ∫ x in B, outerCutoff ε x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) :=
          setIntegral_mono_set hE ((ae_restrict_iff' hBm).2 (Eventually.of_forall hnonneg))
            (Eventually.of_forall hUB)
  have h2 := S.caccioppoli hε n (by linarith)
  -- the cutoff gradient lives on `B \ B_{ε/2}`
  set T := B \ euclideanBall (0 : Vec d) (ε / 2)
  have hTm : MeasurableSet T := hBm.diff (measurableSet_euclideanBall _ _)
  have hwT : MemL2On T w := (S.G n).toH1Function.memL2.mono_measure
    (Measure.restrict_mono Set.sdiff_subset le_rfl)
  have hωη : MemVectorL2On B (fun x => w x • classicalGradient (outerCutoff ε) x) := fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
      Ch4Infra.memL2On_mul_partialDeriv (outerCutoff_eucLip hε) (by positivity)
        (S.G n).toH1Function.memL2 i
  have hQ : IntegrableOn
      (fun x => w x ^ 2 * vecNormSq (classicalGradient (outerCutoff ε) x)) B := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hωη
  have hwsq : Integrable (fun x => w x ^ 2) (volume.restrict B) :=
    (S.G n).toH1Function.memL2.integrable_sq
  have h3 : ∫ x in B, w x ^ 2 * vecNormSq (classicalGradient (outerCutoff ε) x) ≤
      (2 / ε) ^ 2 * ∫ x in T, w x ^ 2 := by
    rw [← integral_const_mul]
    have hind : ∫ x in T, (2 / ε) ^ 2 * w x ^ 2 =
        ∫ x in B, T.indicator (fun x => (2 / ε) ^ 2 * w x ^ 2) x := by
      rw [setIntegral_indicator hTm, Set.inter_eq_right.2 Set.sdiff_subset]
    rw [hind]
    refine setIntegral_mono_on hQ ((hwsq.const_mul _).indicator hTm) hBm fun x hx => ?_
    by_cases hxT : x ∈ T
    · rw [Set.indicator_of_mem hxT, mul_comm ((2 / ε) ^ 2)]
      exact mul_le_mul_of_nonneg_left (vecNormSq_classicalGradient_outerCutoff_le hε x)
        (sq_nonneg _)
    · rw [Set.indicator_of_notMem hxT]
      have hxb : x ∈ euclideanBall (0 : Vec d) (ε / 2) := by
        by_contra h
        exact hxT ⟨hx, h⟩
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero] at hxb
      rw [classicalGradient_outerCutoff_eq_zero hε hxb]
      simp [vecNormSq]
  have h4 : ∫ x in T, w x ^ 2 ≤ poleConst C Λ (ε / 2) S.E d ^ 2 := by
    rw [← toReal_eLpNorm_two_sq_eq_integral_sq hwT]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg
      (hL2 (by linarith) (by linarith) n (by linarith)) 2
  have hΛ0 : 0 ≤ 4 * Λ := by linarith
  calc ∫ x in U, vecNormSq (ξ x)
      ≤ ∫ x in B, outerCutoff ε x ^ 2 * vecDot (ξ x) (matVecMul (a x) (ξ x)) := h1
    _ ≤ 4 * Λ * ∫ x in B, w x ^ 2 * vecNormSq (classicalGradient (outerCutoff ε) x) := by
        have := h2
        norm_num at this
        linarith
    _ ≤ 4 * Λ * ((2 / ε) ^ 2 * ∫ x in T, w x ^ 2) := mul_le_mul_of_nonneg_left h3 hΛ0
    _ ≤ 4 * Λ * ((2 / ε) ^ 2 * poleConst C Λ (ε / 2) S.E d ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) hΛ0
    _ = 4 * Λ * (2 / ε) ^ 2 * poleConst C Λ (ε / 2) S.E d ^ 2 := by ring

end ApproxSetting

end PDE.Ch4Green
