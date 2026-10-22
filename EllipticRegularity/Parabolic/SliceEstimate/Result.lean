module

public import EllipticRegularity.Parabolic.SliceEstimate.Assembly
public import EllipticRegularity.Parabolic.Caccioppoli.Assembly

/-!
# The time slice estimate (Lemma 5.10)

`PDE.Parabolic.slice_estimate` is the full proof of the statement
`PDE.parabSliceEstimate`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Slice

/-- Boundedness gives a finite essential supremum. -/
theorem essSup_lt_top_of_bound {d : ℕ} {f : Vec d × ℝ → ℝ} {C : ℝ}
    (hC : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |f z| ≤ C) :
    eLpNormEssSup f (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) < ⊤ :=
  eLpNormEssSup_lt_top_of_ae_bound (C := C) (by
    filter_upwards [ae_mem_cyl] with z hz
    simpa [Real.norm_eq_abs] using hC z hz)

theorem ae_abs_le_essSup {d : ℕ} {f : Vec d × ℝ → ℝ}
    (hf : eLpNormEssSup f (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) < ⊤) :
    ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      |f z| ≤ (eLpNormEssSup f
        (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))).toReal := by
  filter_upwards [ae_le_eLpNormEssSup (f := f)
    (μ := volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))] with z hz
  rw [Real.enorm_eq_ofReal_abs] at hz
  exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 hz


/-- Lemma 5.10 (statement of `PDE.parabSliceEstimate`). -/
theorem slice_estimate (d : ℕ) (lam Lam : ℝ) (a₀ : Vec d → Mat d)
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hφ : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, |φ.toFun z| ≤ 1) :
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 ∩ {z | φ.toFun z ≠ 0},
        ENNReal.ofReal (vecDot (u.grad z)
          (matVecMul (symmPart (a₀ z.1)) (u.grad z)))) < ⊤ ∧
    ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      (∫⁻ x in euclideanBall (0 : Vec d) 1,
          ENNReal.ofReal (φ.toFun (x, t) ^ 4 * vecDot (u.grad (x, t))
            (matVecMul (symmPart (a₀ x)) (u.grad (x, t)))))
        ≤ 7 * ENNReal.ofReal (Lam / lam) *
          (4 * eLpNormEssSup (fun z => parTimeDeriv φ.toFun z)
              (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) +
            16 * ENNReal.ofReal Lam *
              eLpNormEssSup (fun z => Real.sqrt (vecNormSq (parSpaceGrad φ.toFun z)))
                (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) ^ 2) *
          ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 ∩ {z | φ.toFun z ≠ 0},
            ENNReal.ofReal (vecDot (u.grad z)
              (matVecMul (symmPart (a₀ z.1)) (u.grad z))) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  set ν : Measure (Vec d × ℝ) :=
    volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) with hν
  have hmS : MeasurableSet {z : Vec d × ℝ | φ.toFun z ≠ 0} :=
    (isClosed_eq φ.contDiff.continuous continuous_const).isOpen_compl.measurableSet
  have hmBJ : MeasurableSet (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    hU.measurableSet.prod measurableSet_Ioc
  obtain ⟨hlam, hlamLam⟩ := lam_facts ha
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  -- the essential suprema
  obtain ⟨C, hC0, hC⟩ := PDE.ParabCaccioppoli.exists_bound hU φ
  have hE1 : eLpNormEssSup (fun z => parTimeDeriv φ.toFun z) ν < ⊤ :=
    essSup_lt_top_of_bound (C := C) fun z hz =>
      PDE.ParabCaccioppoli.abs_parTimeDeriv_le φ z C (hC z hz).2
  have hE2 : eLpNormEssSup (fun z => Real.sqrt (vecNormSq (parSpaceGrad φ.toFun z))) ν < ⊤ :=
    essSup_lt_top_of_bound (C := Real.sqrt (d * C ^ 2)) fun z hz => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (PDE.ParabCaccioppoli.vecNormSq_parSpaceGrad_le φ z C (hC z hz).2)
  set c1 : ℝ := (eLpNormEssSup (fun z => parTimeDeriv φ.toFun z) ν).toReal with hc1def
  set c2 : ℝ := (eLpNormEssSup (fun z => Real.sqrt (vecNormSq (parSpaceGrad φ.toFun z))) ν).toReal
    with hc2def
  have hc1 : 0 ≤ c1 := ENNReal.toReal_nonneg
  have hc2 : 0 ≤ c2 := ENNReal.toReal_nonneg
  have h1 : ∀ᵐ z ∂ν, |parTimeDeriv φ.toFun z| ≤ c1 := ae_abs_le_essSup hE1
  have h2 : ∀ᵐ z ∂ν, vecNormSq (parSpaceGrad φ.toFun z) ≤ c2 ^ 2 := by
    filter_upwards [ae_abs_le_essSup hE2] with z hz
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hz
    calc vecNormSq (parSpaceGrad φ.toFun z) = (Real.sqrt (vecNormSq (parSpaceGrad φ.toFun z))) ^ 2 :=
          (Real.sq_sqrt (vecNormSq_nonneg _)).symm
      _ ≤ c2 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hz 2
  have hreal := slice_real ha u v hu hv φ hφ hc1 h1 h2
  set G0 : ℝ := ∫ z, {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
    (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z ∂ν with hG0
  have hmeasφ : Continuous φ.toFun := φ.contDiff.continuous
  have hiAu : Integrable (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) ν := by
    have := integrable_qf_global ha u (ω := fun _ => 1) continuous_const.aestronglyMeasurable
      (M := 1) (Eventually.of_forall fun z => by simp)
    simpa using this
  have hiInd := hiAu.indicator hmS
  have hnnInd : 0 ≤ᵐ[ν] ({z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
      fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) := by
    filter_upwards [ha.elliptic] with z hz
    exact Set.indicator_nonneg (fun z _ => qf_self_nonneg hz _) z
  have hG00 : 0 ≤ G0 := integral_nonneg_of_ae hnnInd
  have hGl : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 ∩ {z | φ.toFun z ≠ 0},
      ENNReal.ofReal (vecDot (u.grad z) (matVecMul (symmPart (a₀ z.1)) (u.grad z))) =
      ENNReal.ofReal G0 := by
    rw [hG0, ofReal_integral_eq_lintegral_ofReal hiInd hnnInd]
    have : ∀ z : Vec d × ℝ, ENNReal.ofReal ({z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
        (fun z => qf (a₀ z.1) (u.grad z) (u.grad z)) z) =
        {z : Vec d × ℝ | φ.toFun z ≠ 0}.indicator
          (fun z => ENNReal.ofReal (qf (a₀ z.1) (u.grad z) (u.grad z))) z := fun z => by
      by_cases h : z ∈ {z : Vec d × ℝ | φ.toFun z ≠ 0} <;> simp [h]
    simp_rw [this]
    rw [lintegral_indicator hmS, hν, Measure.restrict_restrict hmS, inter_comm]
    rfl
  refine ⟨by rw [hGl]; exact ENNReal.ofReal_lt_top, ?_⟩
  -- the a.e. estimate
  have hφ4 : ∀ᵐ z ∂ν, |φ.toFun z ^ 4| ≤ 1 := by
    filter_upwards [ae_mem_cyl] with z hz
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hφ z hz)
  have hf4 : Integrable (fun z => φ.toFun z ^ 4 * qf (a₀ z.1) (u.grad z) (u.grad z)) ν :=
    integrable_qf_global ha u (hmeasφ.pow 4).aestronglyMeasurable hφ4
  have hsl : ∀ᵐ t ∂(volume.restrict (Ioc (-1 : ℝ) 0)),
      Integrable (fun x => φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)))
        (volume.restrict (euclideanBall (0 : Vec d) 1)) := by
    have := hf4
    rw [hν, PDE.Parabolic.Energy.volume_restrict_prod] at this
    exact this.prod_left_ae
  have hE1eq : eLpNormEssSup (fun z => parTimeDeriv φ.toFun z) ν = ENNReal.ofReal c1 :=
    (ENNReal.ofReal_toReal hE1.ne).symm
  have hE2eq : eLpNormEssSup (fun z => Real.sqrt (vecNormSq (parSpaceGrad φ.toFun z))) ν =
      ENNReal.ofReal c2 := (ENNReal.ofReal_toReal hE2.ne).symm
  filter_upwards [hreal, hsl] with t ht hit
  have hnn : 0 ≤ᵐ[volume.restrict (euclideanBall (0 : Vec d) 1)]
      fun x => φ.toFun (x, t) ^ 4 * qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)) := by
    filter_upwards [ae_elliptic_space ha] with x hx
    exact mul_nonneg (by positivity) (qf_self_nonneg hx _)
  have e := ofReal_integral_eq_lintegral_ofReal hit hnn
  rw [hE1eq, hE2eq, hGl]
  have hM0 : 0 ≤ 4 * c1 + 16 * Lam * c2 ^ 2 := by positivity
  have hκ0 : 0 ≤ Lam / lam := div_nonneg hLam.le hlam.le
  have e4 : (4 : ℝ≥0∞) * ENNReal.ofReal c1 = ENNReal.ofReal (4 * c1) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have e16 : (16 : ℝ≥0∞) * ENNReal.ofReal Lam * ENNReal.ofReal c2 ^ 2 =
      ENNReal.ofReal (16 * Lam * c2 ^ 2) := by
    rw [← ENNReal.ofReal_pow hc2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp [mul_assoc]
  have eM : 4 * ENNReal.ofReal c1 + 16 * ENNReal.ofReal Lam * ENNReal.ofReal c2 ^ 2 =
      ENNReal.ofReal (4 * c1 + 16 * Lam * c2 ^ 2) := by
    rw [e4, e16, ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [eM]
  have hfin : (7 : ℝ≥0∞) * ENNReal.ofReal (Lam / lam) *
      ENNReal.ofReal (4 * c1 + 16 * Lam * c2 ^ 2) * ENNReal.ofReal G0 =
      ENNReal.ofReal (7 * (Lam / lam) * (4 * c1 + 16 * Lam * c2 ^ 2) * G0) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    simp
  rw [hfin]
  show (∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (φ.toFun (x, t) ^ 4 *
      qf (a₀ x) (u.grad (x, t)) (u.grad (x, t)))) ≤ _
  rw [← e]
  exact ENNReal.ofReal_le_ofReal ht

end PDE.Parabolic
