module

public import EllipticRegularity.Parabolic.SliceEstimate.Bridge
public import EllipticRegularity.Parabolic.SliceEstimate.DataV
public import EllipticRegularity.Parabolic.SliceEstimate.Step2
public import EllipticRegularity.Parabolic.SliceEstimate.TimeEnergyBound
public import EllipticRegularity.Parabolic.SliceEstimate.Cutoff

/-!
# Assembly of the time slice estimate (real-valued form)
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

section Assembly

variable {lam Lam : ℝ} {a₀ : Vec d → Mat d}

/-- The quadratic form of an `L²` gradient is integrable on the whole cylinder. -/
theorem integrable_qf_global
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (w : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) {ω : Vec d × ℝ → ℝ}
    (hω : AEStronglyMeasurable ω
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) {M : ℝ}
    (hM : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)), |ω z| ≤ M) :
    Integrable (fun z => ω z * qf (a₀ z.1) (w.grad z) (w.grad z))
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  have hg2 : ∀ i, Integrable (fun z => w.grad z i ^ 2) ν := fun i => (w.gradMemL2 i).integrable_sq
  have hbound : Integrable (fun z => |M| * Lam * ∑ i, w.grad z i ^ 2) ν :=
    (integrable_finsetSum _ fun i _ => hg2 i).const_mul _
  have hmeas : AEStronglyMeasurable (fun z => ω z * qf (a₀ z.1) (w.grad z) (w.grad z)) ν := by
    refine hω.mul ?_
    have : ∀ z, qf (a₀ z.1) (w.grad z) (w.grad z) =
        ∑ i, ∑ j, symmPart (a₀ z.1) i j * (w.grad z i * w.grad z j) := fun z => by
      simp only [qf, vecDot, matVecMul, symmPart, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [this]
    refine (Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => ?_).aestronglyMeasurable
    have h1 : AEMeasurable (fun z : Vec d × ℝ => symmPart (a₀ z.1) i j) ν := by
      simp only [symmPart]
      exact ((ha.measurable i j).add (ha.measurable j i)).div_const 2
    exact h1.mul (((w.gradMemL2 i).aestronglyMeasurable.aemeasurable).mul
      ((w.gradMemL2 j).aestronglyMeasurable.aemeasurable))
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards [hM, ha.elliptic] with z hz hell
  rw [Real.norm_eq_abs, abs_mul]
  have h0 := qf_self_nonneg hell (w.grad z)
  have h1 := qf_le_Lam_normSq hell (w.grad z)
  have hsq : vecNormSq (w.grad z) = ∑ i, w.grad z i ^ 2 := vecNormSq_eq_sum_sq _
  rw [abs_of_nonneg h0]
  have : |ω z| ≤ |M| := hz.trans (le_abs_self M)
  calc |ω z| * qf (a₀ z.1) (w.grad z) (w.grad z)
      ≤ |M| * (Lam * vecNormSq (w.grad z)) :=
        mul_le_mul this h1 h0 (abs_nonneg _)
    _ = |M| * Lam * ∑ i, w.grad z i ^ 2 := by rw [hsq]; ring


theorem ae_mem_cyl : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
    z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
  ae_restrict_mem ((isOpen_euclideanBall _ _).measurableSet.prod measurableSet_Ioc)

/-- `∫ φ⁴ B ≤ M ∫ φ² v²` from the Caccioppoli inequality for `v` with cutoff `φ²`. -/
theorem bphi_le
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hφ1 : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |φ.toFun z| ≤ 1)
    {c1 c2 : ℝ} (hc1 : 0 ≤ c1)
    (h1 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      |parTimeDeriv φ.toFun z| ≤ c1)
    (h2 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      vecNormSq (parSpaceGrad φ.toFun z) ≤ c2 ^ 2) :
    (Integrable (fun z => φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z))
      (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) ∧
    ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)
        ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ≤
      (4 * c1 + 16 * Lam * c2 ^ 2) * ∫ z, φ.toFun z ^ 2 * v.toFun z ^ 2
        ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  have hmeasφ : Continuous φ.toFun := φ.contDiff.continuous
  have hφ4 : ∀ᵐ z ∂ν, |φ.toFun z ^ 4| ≤ 1 := by
    filter_upwards [ae_mem_cyl] with z hz
    have := hφ1 z hz
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) this
  have hint1 : Integrable (fun z => φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)) ν :=
    integrable_qf_global ha v (hmeasφ.pow 4).aestronglyMeasurable hφ4
  refine ⟨hint1, ?_⟩
  have hnn : 0 ≤ᵐ[ν] fun z => φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) := by
    filter_upwards [ha.elliptic] with z hz
    exact mul_nonneg (by positivity) (qf_self_nonneg hz _)
  have hint2 : Integrable (fun z => φ.toFun z ^ 2 * v.toFun z ^ 2) ν := by
    have hφ2 : ∀ᵐ z ∂ν, ‖φ.toFun z ^ 2‖ ≤ 1 := by
      filter_upwards [ae_mem_cyl] with z hz
      have := hφ1 z hz
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) this
    exact (v.memL2.integrable_sq).bdd_mul (hmeasφ.pow 2).aestronglyMeasurable hφ2
  -- Caccioppoli for `v` with cutoff `φ²`
  have cacc := PDE.Parabolic.caccioppoli_of_energy_identity d lam Lam
    (fun z : Vec d × ℝ => a₀ z.1) ha v (sqCutoff φ) 0 ⟨by norm_num, le_rfl⟩
    (energyConclusion_v ha u v hu hv (sqCutoff φ))
  obtain ⟨hc, -⟩ := cacc
  have hc' := le_trans le_self_add hc
  -- rewrite the integrands
  have e1 : ∀ z : Vec d × ℝ, ENNReal.ofReal ((sqCutoff φ).toFun z ^ 2 *
      vecDot (v.grad z) (matVecMul ((fun z : Vec d × ℝ => a₀ z.1) z) (v.grad z))) =
      ENNReal.ofReal (φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)) := by
    intro z
    rw [qf_self]
    congr 1
    show (φ.toFun z ^ 2) ^ 2 * _ = _
    ring
  simp only [e1] at hc'
  set M : ℝ := 4 * c1 + 16 * Lam * c2 ^ 2 with hM
  have hbound : ∀ᵐ z ∂ν, ENNReal.ofReal (v.toFun z ^ 2 *
      (2 * |(sqCutoff φ).toFun z| * |parTimeDeriv (sqCutoff φ).toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad (sqCutoff φ).toFun z))) ≤
      ENNReal.ofReal (M * (φ.toFun z ^ 2 * v.toFun z ^ 2)) := by
    filter_upwards [ae_mem_cyl, h1, h2] with z hz hz1 hz2
    refine ENNReal.ofReal_le_ofReal ?_
    have hφz := hφ1 z hz
    have hLam : 0 < Lam := PDE.ParabCaccioppoli.Lam_pos_of_coeff ha
    have ht : parTimeDeriv (sqCutoff φ).toFun z = 2 * φ.toFun z * parTimeDeriv φ.toFun z :=
      parTimeDeriv_sq φ.toFun φ.contDiff z
    have hs : vecNormSq (parSpaceGrad (sqCutoff φ).toFun z) =
        4 * φ.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z) := by
      have : parSpaceGrad (sqCutoff φ).toFun z = (2 * φ.toFun z) • parSpaceGrad φ.toFun z := by
        ext i
        rw [Pi.smul_apply, smul_eq_mul]
        exact parSpaceGrad_sq φ.toFun φ.contDiff z i
      rw [this, vecNormSq_smul]; ring
    rw [ht, hs]
    show v.toFun z ^ 2 * (2 * |φ.toFun z ^ 2| * |2 * φ.toFun z * parTimeDeriv φ.toFun z| +
        4 * Lam * (4 * φ.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z))) ≤ _
    have habs1 : |φ.toFun z ^ 2| = φ.toFun z ^ 2 := abs_of_nonneg (sq_nonneg _)
    have habs2 : |2 * φ.toFun z * parTimeDeriv φ.toFun z| =
        2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| := by
      rw [abs_mul, abs_mul, abs_two]
    rw [habs1, habs2]
    have hq : φ.toFun z ^ 2 = |φ.toFun z| ^ 2 := (sq_abs _).symm
    have hN := vecNormSq_nonneg (parSpaceGrad φ.toFun z)
    set t := |φ.toFun z| with ht'
    have ht0 : 0 ≤ t := abs_nonneg _
    have h3 : t ^ 3 * |parTimeDeriv φ.toFun z| ≤ t ^ 2 * c1 := by
      calc t ^ 3 * |parTimeDeriv φ.toFun z| ≤ t ^ 2 * |parTimeDeriv φ.toFun z| :=
            mul_le_mul_of_nonneg_right
              (by have h := mul_le_mul_of_nonneg_left hφz (sq_nonneg t); linarith) (abs_nonneg _)
        _ ≤ t ^ 2 * c1 := mul_le_mul_of_nonneg_left hz1 (sq_nonneg _)
    have h4 : φ.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z) ≤ φ.toFun z ^ 2 * c2 ^ 2 :=
      mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)
    have hv2 := sq_nonneg (v.toFun z)
    have key : 2 * φ.toFun z ^ 2 * (2 * t * |parTimeDeriv φ.toFun z|) +
        4 * Lam * (4 * φ.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z)) ≤
        M * φ.toFun z ^ 2 := by
      rw [hq] at h4 ⊢
      rw [hM]
      have h5 := mul_le_mul_of_nonneg_left h4 hLam.le
      linarith [h3, h5]
    calc v.toFun z ^ 2 * (2 * φ.toFun z ^ 2 * (2 * t * |parTimeDeriv φ.toFun z|) +
          4 * Lam * (4 * φ.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z)))
        ≤ v.toFun z ^ 2 * (M * φ.toFun z ^ 2) := mul_le_mul_of_nonneg_left key hv2
      _ = M * (φ.toFun z ^ 2 * v.toFun z ^ 2) := by ring
  -- conclude
  have hlint : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      ENNReal.ofReal (φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)) ≤
      ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
        ENNReal.ofReal (M * (φ.toFun z ^ 2 * v.toFun z ^ 2)) :=
    hc'.trans (lintegral_mono_ae hbound)
  have hMint : Integrable (fun z => M * (φ.toFun z ^ 2 * v.toFun z ^ 2)) ν := hint2.const_mul M
  have hMnn : 0 ≤ᵐ[ν] fun z => M * (φ.toFun z ^ 2 * v.toFun z ^ 2) := by
    refine Eventually.of_forall fun z => ?_
    have hLam : 0 < Lam := PDE.ParabCaccioppoli.Lam_pos_of_coeff ha
    have hM0 : 0 ≤ M := by rw [hM]; positivity
    positivity
  have e2 := ofReal_integral_eq_lintegral_ofReal hint1 hnn
  have e3 := ofReal_integral_eq_lintegral_ofReal hMint hMnn
  rw [← e2, ← e3] at hlint
  have hM0 : 0 ≤ M := by
    have hLam : 0 < Lam := PDE.ParabCaccioppoli.Lam_pos_of_coeff ha
    rw [hM]; positivity
  have hI2 : 0 ≤ ∫ z, φ.toFun z ^ 2 * v.toFun z ^ 2 ∂ν :=
    integral_nonneg fun z => by positivity
  have := (ENNReal.ofReal_le_ofReal_iff (by rw [integral_const_mul]; positivity)).1 hlint
  rw [integral_const_mul] at this
  exact this


theorem lam_facts
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) : 0 < lam ∧ lam ≤ Lam := by
  have hpos : 0 < volume (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    refine ENNReal.mul_pos ?_ ?_
    · exact ((isOpen_euclideanBall (0 : Vec d) 1).measure_pos volume
        ⟨0, by simp [euclideanBall, euclideanSqDist, vecNormSq_eq_sum_sq]⟩).ne'
    · simp
  have : NeBot (ae (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) :=
    ae_neBot.2 (by simpa [Measure.restrict_eq_zero] using hpos.ne')
  obtain ⟨z, hz⟩ := ha.elliptic.exists
  exact ⟨hz.lam_pos, hz.lam_le_Lam⟩

/-- The auxiliary inequality of Step 2. -/
theorem X_le_aux
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hφ1 : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |φ.toFun z| ≤ 1)
    {c2 : ℝ}
    (h2 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      vecNormSq (parSpaceGrad φ.toFun z) ≤ c2 ^ 2) {θ : ℝ} (hθ : 0 < θ) :
    ∫ z, φ.toFun z ^ 2 * v.toFun z ^ 2
        ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ≤
      θ / 2 * (∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)
        ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) +
      ((Lam / lam) / (2 * θ) + 2 * Lam * c2 ^ 2) *
        (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
          (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z
          ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) +
      (1 / 2) * ∫ z, φ.toFun z ^ 2 * v.toFun z ^ 2
        ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  obtain ⟨hlam, hlamLam⟩ := lam_facts ha
  have hmeasφ : Continuous φ.toFun := φ.contDiff.continuous
  obtain ⟨i1, i2, i3, hsum⟩ := step2_identity ha u v hu hv φ
  have hmS : MeasurableSet {z : Vec d × ℝ | φ.toFun z ≠ 0} :=
    (isClosed_eq hmeasφ continuous_const).isOpen_compl.measurableSet
  have hφ4 : ∀ᵐ z ∂ν, |φ.toFun z ^ 4| ≤ 1 := by
    filter_upwards [ae_mem_cyl] with z hz
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hφ1 z hz)
  have iBv : Integrable (fun z => φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)) ν :=
    integrable_qf_global ha v (hmeasφ.pow 4).aestronglyMeasurable hφ4
  have iAu : Integrable (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) ν := by
    have := integrable_qf_global ha u (ω := fun _ => 1) continuous_const.aestronglyMeasurable
      (M := 1) (Eventually.of_forall fun z => by simp)
    simpa using this
  have iInd : Integrable ({z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z))) ν := iAu.indicator hmS
  -- the pointwise bounds
  have hb2 : ∀ᵐ z ∂ν, |φ.toFun z ^ 2 * vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)| ≤
      θ / 2 * (φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)) +
        (Lam / lam) / (2 * θ) * {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
          (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z := by
    filter_upwards [ha.elliptic] with z hz
    by_cases hφ : φ.toFun z = 0
    · simp [hφ]
    · have hI : {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
          (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z = qf (a₀ z.1) (u.grad z) (u.grad z) :=
        indicator_of_mem (show z ∈ {z : Vec d × ℝ | φ.toFun z ≠ 0} from hφ) _
      rw [hI]
      have hP := sq_vecDot_matVecMul_le hz (u.grad z) (v.grad z)
      have hAu := qf_self_nonneg hz (u.grad z)
      have hBv := qf_self_nonneg hz (v.grad z)
      set Au := qf (a₀ z.1) (u.grad z) (u.grad z)
      set Bv := qf (a₀ z.1) (v.grad z) (v.grad z)
      set P := vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)
      have hκ : 0 ≤ Lam / lam := div_nonneg (hlam.le.trans hlamLam) hlam.le |>.trans' le_rfl
      have hsq : (φ.toFun z ^ 2 * P) ^ 2 ≤ (θ * (φ.toFun z ^ 4 * Bv)) * ((Lam / lam) * Au / θ) := by
        have : (θ * (φ.toFun z ^ 4 * Bv)) * ((Lam / lam) * Au / θ) =
            φ.toFun z ^ 4 * ((Lam / lam) * Au * Bv) := by field_simp
        have h4 : (φ.toFun z ^ 2 * P) ^ 2 = φ.toFun z ^ 4 * P ^ 2 := by ring
        rw [this, h4]
        exact mul_le_mul_of_nonneg_left hP (by positivity)
      have := abs_le_add_halves_of_sq_le_mul hsq (by positivity)
        (by have := hlam.le; positivity)
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)] at this
      have e : (Lam / lam) / (2 * θ) * Au = ((Lam / lam) * Au / θ) / 2 := by field_simp
      rw [e]
      rw [abs_mul, abs_of_nonneg (sq_nonneg (φ.toFun z))]
      linarith [this]
  have hb3 : ∀ᵐ z ∂ν, |2 * φ.toFun z * v.toFun z *
      vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z)| ≤
      (1 / 2) * (φ.toFun z ^ 2 * v.toFun z ^ 2) +
        2 * Lam * c2 ^ 2 * {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
          (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z := by
    filter_upwards [ha.elliptic, h2] with z hz hz2
    have hLam : 0 < Lam := hlam.trans_le hlamLam
    by_cases hφ : φ.toFun z = 0
    · simp [hφ]
    · have hI : {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
          (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z = qf (a₀ z.1) (u.grad z) (u.grad z) :=
        indicator_of_mem (show z ∈ {z : Vec d × ℝ | φ.toFun z ≠ 0} from hφ) _
      rw [hI]
      have hP := sq_vecDot_matVecMul_le_normSq hz (u.grad z) (parSpaceGrad φ.toFun z)
      have hAu := qf_self_nonneg hz (u.grad z)
      set Au := qf (a₀ z.1) (u.grad z) (u.grad z)
      set P := vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z)
      have hP2 : P ^ 2 ≤ Lam * Au * c2 ^ 2 :=
        hP.trans (mul_le_mul_of_nonneg_left hz2 (mul_nonneg hLam.le hAu))
      have hsq : (2 * φ.toFun z * v.toFun z * P) ^ 2 ≤
          (φ.toFun z ^ 2 * v.toFun z ^ 2) * (4 * Lam * c2 ^ 2 * Au) := by
        have : (2 * φ.toFun z * v.toFun z * P) ^ 2 =
            (φ.toFun z ^ 2 * v.toFun z ^ 2) * (4 * P ^ 2) := by ring
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hP2]
      have := abs_le_add_halves_of_sq_le_mul hsq (by positivity)
        (by positivity)
      linarith
  -- integrate
  have iG : Integrable (fun z => θ / 2 * (φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)) +
      (Lam / lam) / (2 * θ) * {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
        (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z) ν :=
    (iBv.const_mul _).add (iInd.const_mul _)
  have iH : Integrable (fun z => (1 / 2) * (φ.toFun z ^ 2 * v.toFun z ^ 2) +
      2 * Lam * c2 ^ 2 * {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
        (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z) ν :=
    (i1.const_mul _).add (iInd.const_mul _)
  have m2 := integral_mono_ae i2.abs iG hb2
  have m3 := integral_mono_ae i3.abs iH hb3
  rw [integral_add (iBv.const_mul _) (iInd.const_mul _), integral_const_mul, integral_const_mul]
    at m2
  rw [integral_add (i1.const_mul _) (iInd.const_mul _), integral_const_mul, integral_const_mul]
    at m3
  have a2 : |∫ z, φ.toFun z ^ 2 * vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z) ∂ν| ≤
      ∫ z, |φ.toFun z ^ 2 * vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z)| ∂ν :=
    abs_integral_le_integral_abs
  have a3 : |∫ z, 2 * φ.toFun z * v.toFun z *
      vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z) ∂ν| ≤
      ∫ z, |2 * φ.toFun z * v.toFun z *
        vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z)| ∂ν :=
    abs_integral_le_integral_abs
  have hX : ∫ z, φ.toFun z ^ 2 * v.toFun z ^ 2 ∂ν =
      -(∫ z, φ.toFun z ^ 2 * vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z) ∂ν) -
        ∫ z, 2 * φ.toFun z * v.toFun z *
          vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z) ∂ν := by
    linarith [hsum]
  have hl2 := neg_abs_le (∫ z, φ.toFun z ^ 2 * vecDot (matVecMul (a₀ z.1) (u.grad z)) (v.grad z) ∂ν)
  have hl3 := neg_abs_le (∫ z, 2 * φ.toFun z * v.toFun z *
    vecDot (matVecMul (a₀ z.1) (u.grad z)) (parSpaceGrad φ.toFun z) ∂ν)
  have hcomb : (Lam / lam) / (2 * θ) * (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν) +
      2 * Lam * c2 ^ 2 * (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν) =
      ((Lam / lam) / (2 * θ) + 2 * Lam * c2 ^ 2) * (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν) := by ring
  linarith [hX, m2, m3, a2, a3, hl2, hl3, hcomb]


/-- The time slice energy is bounded by `G` and `∫ φ⁴ B` (for every `ε > 0`). -/
theorem E_le_eps
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hφ1 : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |φ.toFun z| ≤ 1)
    {c1 : ℝ} (hc1 : 0 ≤ c1)
    (h1 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      |parTimeDeriv φ.toFun z| ≤ c1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))) ≤
        (4 * c1 + ε⁻¹) * (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
            (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z
            ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) +
          ε * ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z)
            ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) := by
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  obtain ⟨D, hDA, hDφ, hDl, hDL, hDq, hDK, hDp1, hDp0, hDW, hDZ, hvanK, hvanp⟩ :=
    exists_edata ha u v hv φ
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hmeasBJ : MeasurableSet (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    hU.measurableSet.prod measurableSet_Ioc
  have hWv : ∀ z, D.Wv z = u.grad z := fun z => by
    ext i; exact congrFun (hDW i) z
  have hZv : ∀ z, D.Zv z = v.grad z := fun z => by
    ext i; exact congrFun (hDZ i) z
  have hμle : D.μ D.q ≤ ν := by
    rw [hDq]
    exact Measure.restrict_mono (prod_mono hDK (Ioc_subset_Ioc_left hDp1.le)) le_rfl
  have hh1 : ∀ᵐ z ∂(D.μ D.q), |parTimeDeriv D.φ z| ≤ c1 := by
    rw [hDφ]; exact (ae_mono hμle) h1
  have hhφ : ∀ᵐ z ∂(D.μ D.q), |D.φ z| ≤ 1 := by
    rw [hDφ]
    have : ∀ᵐ z ∂ν, |φ.toFun z| ≤ 1 := by
      filter_upwards [ae_mem_cyl] with z hz using hφ1 z hz
    exact (ae_mono hμle) this
  have key := D.time_energy_bound hε hh1 hhφ
  -- convert the integrals
  have conv : ∀ f : Vec d × ℝ → ℝ, (∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      φ.toFun z = 0 → f z = 0) → ∫ z, f z ∂(D.μ D.q) = ∫ z, f z ∂ν := by
    intro f hf
    have hsub : D.K ×ˢ Ioc D.p 0 ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
      prod_mono hDK (Ioc_subset_Ioc_left hDp1.le)
    have : ∫ z, f z ∂(D.μ D.q) = ∫ z in D.K ×ˢ Ioc D.p 0, f z := by rw [hDq]
    rw [this, hν]
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasBJ hsub ?_
    intro z hz
    apply hf z hz.1
    by_contra hφz
    rcases hz with ⟨⟨hx, hτ⟩, hn⟩
    by_cases hxK : z.1 ∈ D.K
    · by_cases hτp : D.p < z.2
      · exact hn ⟨hxK, hτp, hτ.2⟩
      · exact hφz (hvanp z.1 hx z.2 hτ (not_lt.mp hτp))
    · exact hφz (hvanK z.1 hx hxK z.2 hτ)
  have cG : ∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂(D.μ D.q) =
      ∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν :=
    conv (fun z => {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z) (fun z hz hφ => by simp [hφ])
  have cB : ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) ∂(D.μ D.q) =
      ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) ∂ν :=
    conv (fun z => φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z))
      (fun z hz hφ => by simp [hφ])
  simp only [hDA, hDφ, hWv, hZv] at key
  rw [cG, cB] at key
  -- nonnegativity of the right-hand side
  have hG0 : 0 ≤ ∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha.elliptic] with z hz
    exact Set.indicator_nonneg (fun z _ => qf_self_nonneg hz _) z
  have hB0 : 0 ≤ ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) ∂ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha.elliptic] with z hz
    exact mul_nonneg (by positivity) (qf_self_nonneg hz _)
  have hR0 : 0 ≤ (4 * c1 + ε⁻¹) * (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν) +
      ε * ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) ∂ν := by positivity
  -- relate the energy
  have hEu : ∀ t ∈ Ioc (-1 : ℝ) 0, D.Eu t = ∫ x in euclideanBall (0 : Vec d) 1,
      φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)) := by
    intro t ht
    unfold EData.Eu
    simp only [hDA, hDφ, hWv]
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hDK fun x hx => ?_
    rw [hvanK x hx.1 hx.2 t ht]; simp
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc D.p 0 → D.Eu t ≤
      (4 * c1 + ε⁻¹) * (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
        (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν) +
        ε * ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) ∂ν := by
    rw [hDq] at key
    exact (ae_restrict_iff' measurableSet_Ioc).1 key
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht htJ
  by_cases htp : D.p < t
  · rw [← hEu t htJ]
    exact ht ⟨htp, htJ.2⟩
  · have : ∫ x in euclideanBall (0 : Vec d) 1,
        φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)) =
        ∫ x in euclideanBall (0 : Vec d) 1, (0 : ℝ) := by
      refine setIntegral_congr_fun hU.measurableSet fun x hx => ?_
      show φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)) = 0
      rw [hvanp x hx t htJ (not_lt.mp htp)]; simp
    rw [this, integral_zero]; exact hR0


/-- The real-valued time slice estimate. -/
theorem slice_real
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hφ1 : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |φ.toFun z| ≤ 1)
    {c1 c2 : ℝ} (hc1 : 0 ≤ c1)
    (h1 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      |parTimeDeriv φ.toFun z| ≤ c1)
    (h2 : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      vecNormSq (parSpaceGrad φ.toFun z) ≤ c2 ^ 2) :
    ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))) ≤
        7 * (Lam / lam) * (4 * c1 + 16 * Lam * c2 ^ 2) *
          (∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
            (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z
            ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) := by
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  obtain ⟨hlam, hlamLam⟩ := lam_facts ha
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  obtain ⟨hBint, hBle⟩ := bphi_le ha u v hu hv φ hφ1 hc1 h1 h2
  set M : ℝ := 4 * c1 + 16 * Lam * c2 ^ 2 with hM
  set G0 : ℝ := ∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
    (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν with hG0def
  set Bφ : ℝ := ∫ z, φ.toFun z ^ 4 * qf (a₀ z.1) (v.grad z) (v.grad z) ∂ν with hBdef
  set X : ℝ := ∫ z, φ.toFun z ^ 2 * v.toFun z ^ 2 ∂ν with hXdef
  have hG0 : 0 ≤ G0 := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha.elliptic] with z hz
    exact Set.indicator_nonneg (fun z _ => qf_self_nonneg hz _) z
  have hB0 : 0 ≤ Bφ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha.elliptic] with z hz
    exact mul_nonneg (by positivity) (qf_self_nonneg hz _)
  have hX0 : 0 ≤ X := integral_nonneg fun z => by positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hκ : 1 ≤ Lam / lam := (one_le_div hlam).2 hlamLam
  rcases hM0.eq_or_lt with hMz | hMpos
  · -- `M = 0`
    have hc1z : c1 = 0 := by
      have : 4 * c1 + 16 * Lam * c2 ^ 2 = 0 := by rw [← hM]; exact hMz.symm
      have h3 : 0 ≤ 16 * Lam * c2 ^ 2 := by positivity
      linarith
    have hBz : Bφ ≤ 0 := by rw [← hMz, zero_mul] at hBle; exact hBle
    have hBz' : Bφ = 0 := le_antisymm hBz hB0
    have hall : ∀ n : ℕ, ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
        (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))) ≤
          (4 * c1 + ((n : ℝ) + 1)⁻¹) * G0 + ((n : ℝ) + 1) * Bφ := fun n =>
      E_le_eps ha u v hv φ hφ1 hc1 h1 (by positivity)
    filter_upwards [ae_all_iff.2 hall] with t ht
    rw [← hMz, mul_zero, zero_mul]
    by_contra hpos
    have hpos := not_le.mp hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (G0 / (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))))
    have h5 := ht n
    rw [hc1z, hBz'] at h5
    simp only [mul_zero, add_zero, zero_add] at h5
    have h6 : G0 < ((n : ℝ) + 1) * (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))) := by
      rw [div_lt_iff₀ hpos] at hn
      linarith
    have h7 : (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))) ≤
        ((n : ℝ) + 1)⁻¹ * G0 := h5
    have h8 : ((n : ℝ) + 1) * (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t))) ≤ G0 := by
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      calc ((n : ℝ) + 1) * (∫ x in euclideanBall (0 : Vec d) 1,
          φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)))
          ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * G0) := mul_le_mul_of_nonneg_left h7 hn1.le
        _ = G0 := by field_simp
    linarith
  · -- `M > 0`
    have hε : 0 < 1 / M := by positivity
    have hθ : 0 < 1 / (2 * M) := by positivity
    have hE := E_le_eps ha u v hv φ hφ1 hc1 h1 hε
    have hX := X_le_aux ha u v hu hv φ hφ1 h2 hθ
    have hc2M : 16 * Lam * c2 ^ 2 ≤ M := by rw [hM]; linarith
    have hc1M : 4 * c1 ≤ M := by rw [hM]; have : 0 ≤ 16 * Lam * c2 ^ 2 := by positivity
                                 linarith
    have hinv : (1 / M)⁻¹ = M := by rw [one_div, inv_inv]
    rw [hinv] at hE
    -- numerics
    have hB1 : 1 / M * Bφ ≤ X := by
      calc 1 / M * Bφ ≤ 1 / M * (M * X) := mul_le_mul_of_nonneg_left hBle (by positivity)
        _ = X := by field_simp
    have hB2 : 1 / (2 * M) / 2 * Bφ ≤ X / 4 := by
      have : 1 / (2 * M) / 2 * Bφ = (1 / M * Bφ) / 4 := by field_simp; ring
      rw [this]; linarith
    have hκM : (Lam / lam) / (2 * (1 / (2 * M))) = (Lam / lam) * M := by field_simp
    rw [hκM] at hX
    have hXb : X ≤ 4 * ((Lam / lam) * M + 2 * Lam * c2 ^ 2) * G0 := by
      linarith [hX, hB2]
    filter_upwards [hE] with t ht
    have h9 : (4 * c1 + M) * G0 ≤ 2 * M * G0 := by have := mul_le_mul_of_nonneg_right hc1M hG0; linarith
    have h10 : 4 * ((Lam / lam) * M + 2 * Lam * c2 ^ 2) * G0 ≤
        (4 * (Lam / lam) * M + M / 2) * G0 := by have := mul_le_mul_of_nonneg_right hc2M hG0; linarith
    have h11 : (2 * M + 4 * (Lam / lam) * M + M / 2) * G0 ≤ 7 * (Lam / lam) * M * G0 := by
      have h12 := mul_nonneg (sub_nonneg.2 hκ) (mul_nonneg hMpos.le hG0)
      have h13 := mul_nonneg hMpos.le hG0
      linarith
    linarith [ht, hB1, hXb, h9, h10, h11]

end Assembly

end PDE.Parabolic.Slice
