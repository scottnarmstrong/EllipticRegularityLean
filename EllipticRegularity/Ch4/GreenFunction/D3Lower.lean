module

public import EllipticRegularity.Ch4.GreenFunction.D3Cutoff
public import EllipticRegularity.Ch4.GreenFunction.D3Harnack
public import PDEFoundation.PDE.Ch4.SqTest

/-!
# The lower bound of Proposition 4.42 (Step 2): flux versus Caccioppoli

The flux identity with the cutoff `φ = fluxCutoff r` gives `1 ≤ (2/r) ∫_E |a∇G|` on the closed
shell `E = {r/2 ≤ |x| ≤ r}`; Cauchy–Schwarz and `|aξ|² ≤ Λ ξ·aξ` give
`1 ≤ (2/r)² |E| Λ ∫_E ∇G·a∇G`, and Caccioppoli's inequality with `η = shellCutoff r` bounds the
last integral by `4Λ (6/r)² M² |D_r|` whenever `G ≤ M` a.e. on `D_r = B_{3r/2} \ B_{r/4}`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The closed shell `{r/2 ≤ |x| ≤ r}`. -/
def closedShell (d : ℕ) (r : ℝ) : Set (Vec d) :=
  euclideanClosedBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)

theorem measurableSet_closedShell (r : ℝ) : MeasurableSet (closedShell d r) :=
  (measurableSet_euclideanClosedBall _ _).diff (measurableSet_euclideanBall _ _)

theorem mem_closedShell_iff {r : ℝ} (hr : 0 < r) {x : Vec d} :
    x ∈ closedShell d r ↔ r / 2 ≤ vecEuclideanNorm x ∧ vecEuclideanNorm x ≤ r := by
  rw [closedShell, Set.mem_sdiff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le,
    mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), sub_zero, not_lt, and_comm]

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Caccioppoli on the shell**: `∫_E ∇H·a∇H ≤ 4Λ (6/r)² M² |D_r|`. -/
theorem shell_energy_le (S : ApproxSetting d Λ R a) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R / 2)
    (H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)))
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)) H 0 0)
    {M : ℝ}
    (hHM : ∀ᵐ x ∂volumeOn
        (euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)),
      0 ≤ H.toFun x ∧ H.toFun x ≤ M) :
    ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x)) ≤
      4 * Λ * (6 / r) ^ 2 * M ^ 2 *
        (volume (euclideanBall (0 : Vec d) (3 * r / 2) \
          euclideanBall (0 : Vec d) (r / 4))).toReal := by
  have hR := S.hR
  have hΛ := S.one_le_Lam
  have hUo : IsOpen (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)) :=
      (isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)
  have hUB : (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)) ⊆
      euclideanBall (0 : Vec d) R := Set.sdiff_subset
  have hmeasU : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R \
      euclideanClosedBall (0 : Vec d) (r / 2 / 2))) :=
    fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hUB le_rfl)
  have hellU : ∀ x ∈ (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
      IsEllipticMatrix 1 Λ (a x) := fun x hx => S.hell x (hUB hx)
  set D := euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)
  have hDm : MeasurableSet D :=
    (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)
  have hη := shellCutoff_eucLip (d := d) hr
  have hL : (0 : ℝ) ≤ 6 / r := by positivity
  have hηM := abs_shellCutoff_le_one (d := d) r
  have hηc := hasCompactSupport_shellCutoff (d := d) hr
  have hηU : tsupport (shellCutoff (d := d) r) ⊆ (euclideanBall (0 : Vec d) R \ euclideanClosedBall
      (0 : Vec d) (r / 2 / 2)) := by
    refine (tsupport_shellCutoff_subset hr).trans fun x hx => ?_
    rw [Set.mem_sdiff, mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity),
      mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero, not_lt] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]; linarith
    · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero]
      linarith
  have hηcont : Continuous (shellCutoff (d := d) r) := hη.continuous hL
  -- the sq-test identity and absorption
  obtain ⟨-, -, hid⟩ := Ch4Infra.solution_sqTest_lip hUo hmeasU hellU hsol H hη hL hηM hηc hηU
  have hωη : MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 /
      2)) (fun x => H.toFun x • classicalGradient (shellCutoff r) x) :=
    fun i => by
      simpa only [Pi.smul_apply, smul_eq_mul, classicalGradient] using
        Ch4Infra.memL2On_mul_partialDeriv hη hL H.memL2 i
  have hcomm : ∀ x, vecDot (matVecMul (a x) (H.grad x)) (H.grad x) =
      vecDot (H.grad x) (matVecMul (a x) (H.grad x)) := fun x => vecDot_comm _ _
  have htwo : ∀ x, 2 * shellCutoff r x * H.toFun x *
      vecDot (matVecMul (a x) (H.grad x)) (classicalGradient (shellCutoff r) x) =
      2 * (shellCutoff r x * H.toFun x *
        vecDot (matVecMul (a x) (H.grad x)) (classicalGradient (shellCutoff r) x)) :=
    fun x => by ring
  simp_rw [hcomm, htwo] at hid
  rw [integral_const_mul] at hid
  have hcacc := Ch4Infra.absorb_open hUo.measurableSet hmeasU hellU H.gradMemL2 hηcont hηM hωη
    (c₁ := 1) (c₂ := 2) one_pos (by rw [one_mul, hid])
  norm_num at hcacc
  -- the shell energy is controlled by the cutoff energy
  have hEU : closedShell d r ⊆ (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2
      / 2)) := by
    intro x hx
    rw [mem_closedShell_iff hr] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]; linarith
    · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero]
      linarith
  have hF := DGNM.memVectorL2On_matVecMul_of_aemeasurable hUo.measurableSet hmeasU hellU H.gradMemL2
  have hE : IntegrableOn
      (fun x => shellCutoff r x ^ 2 * vecDot (H.grad x) (matVecMul (a x) (H.grad x))) (euclideanBall
          (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)) := by
    have hC : MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 /
        2)) (fun x => shellCutoff r x ^ 2 • H.grad x) := by
      intro i
      simpa only [Pi.smul_apply, smul_eq_mul] using
        Ch4Infra.memL2On_mul_bounded (H.gradMemL2 i)
          (by fun_prop : Continuous fun x => shellCutoff (d := d) r x ^ 2)
          (Ch4Infra.abs_sq_le hηM)
    simpa only [DGNM.vecDot_smul_left] using integrableOn_vecDot_of_memVectorL2On hC hF
  have hnonneg : ∀ x ∈ (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
      0 ≤ shellCutoff r x ^ 2 * vecDot (H.grad x) (matVecMul (a x) (H.grad x)) :=
    fun x hx => mul_nonneg (sq_nonneg _) (DGNM.vecDot_matVecMul_self_nonneg (hellU x hx) _)
  have h1 : ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x)) ≤
      ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
          shellCutoff r x ^ 2 * vecDot (H.grad x) (matVecMul (a x) (H.grad x)) := by
    calc ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x))
        = ∫ x in closedShell d r,
            shellCutoff r x ^ 2 * vecDot (H.grad x) (matVecMul (a x) (H.grad x)) := by
          refine setIntegral_congr_fun (measurableSet_closedShell r) fun x hx => ?_
          have := (mem_closedShell_iff hr).1 hx
          simp only [shellCutoff_eq_one hr this.1 this.2, one_pow, one_mul]
      _ ≤ _ := setIntegral_mono_set hE
          ((ae_restrict_iff' hUo.measurableSet).2 (Eventually.of_forall hnonneg))
          (Eventually.of_forall hEU)
  -- the cutoff-gradient term
  have hQ : IntegrableOn
      (fun x => H.toFun x ^ 2 * vecNormSq (classicalGradient (shellCutoff r) x))
      (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)) := by
    simpa only [vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hωη
  have hDfin : volume D ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ (by positivity))
      (measure_mono Set.sdiff_subset)
  have hHM' : ∀ᵐ x ∂volume, x ∈ D → 0 ≤ H.toFun x ∧ H.toFun x ≤ M :=
    (ae_restrict_iff' hDm).1 hHM
  have h2 : ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
      H.toFun x ^ 2 * vecNormSq (classicalGradient (shellCutoff r) x) ≤
      ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
          D.indicator (fun _ => (6 / r) ^ 2 * M ^ 2) x := by
    have hUfin : volume (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2))
        ≠ ⊤ :=
      ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ hR.le) (measure_mono hUB)
    refine setIntegral_mono_on_ae hQ ?_ hUo.measurableSet ?_
    · exact (integrableOn_const hUfin).indicator hDm
    · filter_upwards [hHM'] with x hx hxU
      by_cases hxs : vecEuclideanNorm x < r / 3 ∨ 4 * r / 3 < vecEuclideanNorm x
      · rw [classicalGradient_shellCutoff_eq_zero hr hxs]
        simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) x
      · push Not at hxs
        have hxD : x ∈ D := by
          refine ⟨?_, ?_⟩
          · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]; linarith
          · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]; linarith
        rw [Set.indicator_of_mem hxD]
        obtain ⟨h0, hM'⟩ := hx hxD
        have hg := vecNormSq_classicalGradient_le_of_eucLip hη hL x
        have hsq : H.toFun x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ h0 hM' 2
        calc H.toFun x ^ 2 * vecNormSq (classicalGradient (shellCutoff r) x)
            ≤ M ^ 2 * (6 / r) ^ 2 :=
              mul_le_mul hsq hg (vecNormSq_nonneg _) (sq_nonneg _)
          _ = (6 / r) ^ 2 * M ^ 2 := by ring
  have h3 : ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
      D.indicator (fun _ => (6 / r) ^ 2 * M ^ 2) x ≤
      (6 / r) ^ 2 * M ^ 2 * (volume D).toReal := by
    rw [integral_indicator hDm, setIntegral_const, smul_eq_mul, Measure.real,
      Measure.restrict_apply hDm, mul_comm]
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hDfin
      (measure_mono Set.inter_subset_left)) (by positivity)
  calc ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x))
      ≤ ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
          shellCutoff r x ^ 2 * vecDot (H.grad x) (matVecMul (a x) (H.grad x)) := h1
    _ ≤ 4 * Λ * ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)),
        H.toFun x ^ 2 * vecNormSq (classicalGradient (shellCutoff r) x) := by
        linarith
    _ ≤ 4 * Λ * ((6 / r) ^ 2 * M ^ 2 * (volume D).toReal) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by linarith)
    _ = _ := by ring

/-- **Flux lower bound**: `1 ≤ (2/r) ∫_E |a∇H|` on the closed shell `E`. -/
theorem one_le_flux_shell (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R / 2)
    (H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2)))
    (hHG : H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \
      euclideanClosedBall (0 : Vec d) (r / 2 / 2))] G) :
    1 ≤ 2 / r * ∫ x in closedShell d r, vecEuclideanNorm (matVecMul (a x) (H.grad x)) := by
  have hR := S.hR
  have hη := fluxCutoff_eucLip (d := d) hr
  have hL : (0 : ℝ) ≤ 2 / r := by positivity
  have hsupp : tsupport (fluxCutoff (d := d) r) ⊆ euclideanBall (0 : Vec d) R :=
    (tsupport_fluxCutoff_subset hr).trans
      (euclideanClosedBall_subset_euclideanBall hr.le (by linarith))
  have hflux := S.isGreen_flux hd hG (ε := r / 2) (half_pos hr) (by linarith) H hHG
    (fluxCutoff r) ⟨_, hη.lipschitzWith hL⟩ (hasCompactSupport_fluxCutoff hr) hsupp
    ⟨1, fun x hx => fluxCutoff_eq_one hr (by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (half_pos hr), sub_zero] at hx
      exact hx.le)⟩
  rw [fluxCutoff_eq_one hr (by rw [vecEuclideanNorm_eq_zero_iff.2 rfl]; positivity)] at hflux
  set T := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) (r / 2)
  have hTm : MeasurableSet T := (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall
      _ _)
  have hET : closedShell d r ⊆ T := by
    intro x hx
    have h := (mem_closedShell_iff hr).1 hx
    refine ⟨?_, ?_⟩
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]; linarith
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (half_pos hr), sub_zero]; linarith
  have hEU : closedShell d r ⊆
      euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2) := by
    intro x hx
    have h := (mem_closedShell_iff hr).1 hx
    refine ⟨?_, ?_⟩
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]; linarith
    · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero]; linarith
  -- integrability of `|a∇H|` on the shell
  have hUB : euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2) ⊆
      euclideanBall (0 : Vec d) R := Set.sdiff_subset
  have haH : MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 /
      2))
      (fun x => matVecMul (a x) (H.grad x)) :=
    DGNM.memVectorL2On_matVecMul_of_aemeasurable
      ((isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)).measurableSet
      (fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hUB le_rfl))
      (fun x hx => S.hell x (hUB hx)) H.gradMemL2
  have hnormL2 : MemL2On (closedShell d r) (fun x => vecEuclideanNorm (matVecMul (a x) (H.grad x)))
      :=
    (GradMemLpOn.memLp_vecEuclideanNorm haH).mono_measure (Measure.restrict_mono hEU le_rfl)
  have hEfin : volume (closedShell d r) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ hR.le)
      (measure_mono (hET.trans Set.sdiff_subset))
  have hnormInt : IntegrableOn (fun x => vecEuclideanNorm (matVecMul (a x) (H.grad x)))
      (closedShell d r) := by
    have : IsFiniteMeasure (volume.restrict (closedShell d r)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hEfin.lt_top⟩
    exact hnormL2.integrable one_le_two
  set g := (closedShell d r).indicator
    (fun x => 2 / r * vecEuclideanNorm (matVecMul (a x) (H.grad x))) with hgdef
  have hgint : IntegrableOn g T :=
    (IntegrableOn.integrable_indicator (show IntegrableOn
      (fun x => 2 / r * vecEuclideanNorm (matVecMul (a x) (H.grad x))) (closedShell d r) volume
      from hnormInt.const_mul (2 / r)) (measurableSet_closedShell r)).integrableOn
  have hle : ‖∫ x in T, vecDot (fun i => fderiv ℝ (fluxCutoff r) x (basisVec i))
      (matVecMul (a x) (H.grad x))‖ ≤ ∫ x in T, g x := by
    refine norm_integral_le_of_norm_le hgint ((ae_restrict_iff' hTm).2
      (Eventually.of_forall fun x hxT => ?_))
    rw [Real.norm_eq_abs]
    by_cases hxE : x ∈ closedShell d r
    · rw [hgdef, Set.indicator_of_mem hxE]
      refine (abs_vecDot_le_vecEuclideanNorm_mul _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hη.vecEuclideanNorm_classicalGradient_le' hL x)
        (vecEuclideanNorm_nonneg _)
    · rw [hgdef, Set.indicator_of_notMem hxE]
      have hx1 : r / 2 ≤ vecEuclideanNorm x := by
        have := hxT.2
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (half_pos hr), sub_zero, not_lt] at this
        exact this
      have hx2 : r < vecEuclideanNorm x := by
        by_contra h
        exact hxE ((mem_closedShell_iff hr).2 ⟨hx1, not_lt.1 h⟩)
      have h0 : (fun i => fderiv ℝ (fluxCutoff (d := d) r) x (basisVec i)) = 0 :=
        classicalGradient_fluxCutoff_eq_zero hr (Or.inr hx2)
      rw [h0, vecDot_zero_left, abs_zero]
  rw [hflux, norm_one] at hle
  refine hle.trans (le_of_eq ?_)
  rw [integral_indicator (measurableSet_closedShell r), Measure.restrict_restrict
    (measurableSet_closedShell r), Set.inter_eq_left.2 hET, integral_const_mul]

/-- **Cauchy–Schwarz on the shell**: `(∫_E |a∇H|)² ≤ |E| Λ ∫_E ∇H·a∇H`. -/
theorem sq_integral_norm_flux_le (S : ApproxSetting d Λ R a) {r : ℝ} (hr : 0 < r)
    (hrR : r ≤ R / 2)
    (H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2))) :
    (∫ x in closedShell d r, vecEuclideanNorm (matVecMul (a x) (H.grad x))) ^ 2 ≤
      (volume (closedShell d r)).toReal *
        (Λ * ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x))) := by
  have hR := S.hR
  have hEU : closedShell d r ⊆
      euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2) := by
    intro x hx
    have h := (mem_closedShell_iff hr).1 hx
    refine ⟨?_, ?_⟩
    · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero]; linarith
    · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity), sub_zero]; linarith
  have hUB : euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (r / 2 / 2) ⊆
      euclideanBall (0 : Vec d) R := Set.sdiff_subset
  have hEB := hEU.trans hUB
  have hEfin : volume (closedShell d r) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclideanBall_ne_top _ hR.le) (measure_mono hEB)
  have haH : MemVectorL2On (closedShell d r) (fun x => matVecMul (a x) (H.grad x)) := fun i =>
    (DGNM.memVectorL2On_matVecMul_of_aemeasurable
      ((isOpen_euclideanBall _ _).sdiff (isClosed_euclideanClosedBall _ _)).measurableSet
      (fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hUB le_rfl))
      (fun x hx => S.hell x (hUB hx)) H.gradMemL2 i).mono_measure
        (Measure.restrict_mono hEU le_rfl)
  have hgL2 : MemL2On (closedShell d r) (fun x => vecEuclideanNorm (matVecMul (a x) (H.grad x))) :=
    GradMemLpOn.memLp_vecEuclideanNorm haH
  have h1L2 : MemL2On (closedShell d r) (fun _ => (1 : ℝ)) := by
    have : IsFiniteMeasure (volume.restrict (closedShell d r)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hEfin.lt_top⟩
    exact memLp_const 1
  have hcs := abs_integral_mul_le h1L2 hgL2
  simp only [one_mul] at hcs
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [sq_abs, mul_pow, toReal_eLpNorm_two_sq_eq_integral_sq h1L2,
    toReal_eLpNorm_two_sq_eq_integral_sq hgL2] at hsq
  have hone : ∫ _ in closedShell d r, (1 : ℝ) ^ 2 = (volume (closedShell d r)).toReal := by
    simp [Measure.real]
  have hgradL2 : MemVectorL2On (closedShell d r) H.grad := fun i =>
    (H.gradMemL2 i).mono_measure (Measure.restrict_mono hEU le_rfl)
  have hgrad : ∫ x in closedShell d r, vecEuclideanNorm (matVecMul (a x) (H.grad x)) ^ 2 ≤
      Λ * ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ (measurableSet_closedShell r) fun x hx => ?_
    · simpa only [vecEuclideanNorm_sq] using integrableOn_vecNormSq_of_memVectorL2On haH
    · exact (integrableOn_vecDot_of_memVectorL2On hgradL2 haH).const_mul Λ
    · rw [vecEuclideanNorm_sq]
      exact vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix (S.hell x (hEB hx)) _
  calc (∫ x in closedShell d r, vecEuclideanNorm (matVecMul (a x) (H.grad x))) ^ 2
      ≤ (∫ _ in closedShell d r, (1 : ℝ) ^ 2) *
          ∫ x in closedShell d r, vecEuclideanNorm (matVecMul (a x) (H.grad x)) ^ 2 := hsq
    _ ≤ _ := by
        rw [hone]
        exact mul_le_mul_of_nonneg_left hgrad ENNReal.toReal_nonneg

/-- **Lower-bound inequality**: if `G ≤ M` a.e. on `D_r`, then
`1 ≤ 576 Λ² |B_{3r/2}|² M² / r⁴`. -/
theorem isGreen_lower_aux (S : ApproxSetting d Λ R a) (hd : 3 ≤ d)
    (hGnn : ∀ n, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ (S.G n).toH1Function.toFun x)
    {G : Vec d → ℝ} (hG : IsGreenFunction a R G) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R / 2) {M : ℝ}
    (hGM : ∀ᵐ x ∂volumeOn
        (euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)),
      G x ≤ M) :
    1 ≤ 576 * Λ ^ 2 * (volume (euclideanBall (0 : Vec d) (3 * r / 2))).toReal ^ 2 / r ^ 4 *
      M ^ 2 := by
  have hR := S.hR
  have hΛ := S.one_le_Lam
  obtain ⟨H, hHG, hHsol, -⟩ := S.exists_harmonic hd hG (ε := r / 2 / 2) (by positivity)
    (by linarith)
  have hflux := S.one_le_flux_shell hd hG hr hrR H (by rw [hHG])
  have hcs := S.sq_integral_norm_flux_le hr hrR H
  set D := euclideanBall (0 : Vec d) (3 * r / 2) \ euclideanBall (0 : Vec d) (r / 4)
  have hDB : D ⊆ euclideanBall (0 : Vec d) R := fun x hx =>
    euclideanBall_mono (by positivity) (by linarith) hx.1
  have hHM : ∀ᵐ x ∂volumeOn D, 0 ≤ H.toFun x ∧ H.toFun x ≤ M := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hDB (S.isGreen_nonneg hd hGnn hG), hGM]
      with x h0 h1
    rw [hHG]
    exact ⟨h0, h1⟩
  have hen := S.shell_energy_le hr hrR H hHsol hHM
  set X := ∫ x in closedShell d r, vecEuclideanNorm (matVecMul (a x) (H.grad x))
  set V := (volume (euclideanBall (0 : Vec d) (3 * r / 2))).toReal
  have hVfin : volume (euclideanBall (0 : Vec d) (3 * r / 2)) ≠ ⊤ :=
    volume_euclideanBall_ne_top _ (by positivity)
  have hEV : (volume (closedShell d r)).toReal ≤ V := by
    refine ENNReal.toReal_mono hVfin (measure_mono fun x hx => ?_)
    have h := (mem_closedShell_iff hr).1 hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]; linarith
  have hDV : (volume D).toReal ≤ V := ENNReal.toReal_mono hVfin (measure_mono Set.sdiff_subset)
  have hX0 : 0 ≤ X := integral_nonneg fun x => vecEuclideanNorm_nonneg _
  have hE0 := (ENNReal.toReal_nonneg : 0 ≤ (volume (closedShell d r)).toReal)
  have hD0 := (ENNReal.toReal_nonneg : 0 ≤ (volume D).toReal)
  set Y := ∫ x in closedShell d r, vecDot (H.grad x) (matVecMul (a x) (H.grad x))
  have h1 : 1 ≤ (2 / r) ^ 2 * X ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hflux 2
    rw [one_pow, mul_pow] at this
    exact this
  have hr4 : 0 < r ^ 4 := by positivity
  calc (1 : ℝ) ≤ (2 / r) ^ 2 * X ^ 2 := h1
    _ ≤ (2 / r) ^ 2 * ((volume (closedShell d r)).toReal * (Λ * Y)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ (2 / r) ^ 2 * ((volume (closedShell d r)).toReal *
          (Λ * (4 * Λ * (6 / r) ^ 2 * M ^ 2 * (volume D).toReal))) := by
        gcongr
    _ ≤ (2 / r) ^ 2 * (V * (Λ * (4 * Λ * (6 / r) ^ 2 * M ^ 2 * V))) := by
        gcongr
    _ = 576 * Λ ^ 2 * V ^ 2 / r ^ 4 * M ^ 2 := by
        field_simp
        ring

end ApproxSetting

end PDE.Ch4Green
