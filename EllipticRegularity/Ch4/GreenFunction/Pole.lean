module

public import EllipticRegularity.Ch4.GreenFunction.Average
public import EllipticRegularity.Ch4.GreenFunction.Interface
public import EllipticRegularity.DeGiorgi.Assembly.EssContinuous
public import DGNMStatements.DeGiorgiHolder

/-!
# The value at the pole (Lemma 4.38)

If `v ∈ H¹₀(B_R)` solves `-div (b ∇ v) = g` and `g = 0` a.e. in `B_ε`, then `v` is `b`-harmonic in
`B_ε`; by De Giorgi's theorem (applied to a rescaling) it has a representative continuous in
`B_{ε/2}`, bounded by `C Λ^{d/4} ε^{-d/2} ‖v‖_{L²(B_R)}`.  Consequently the averages of `v` over
`B_ρ(0)`, `ρ ≤ ε/2`, are bounded by the same quantity and converge as `ρ → 0`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- An `H¹₀` solution whose source vanishes a.e. on an open subset is a homogeneous solution
there (tested with smooth functions). -/
theorem solutionOn_of_source_ae_zero {b : CoeffField d} {U V : Set (Vec d)} (hV : IsOpen V)
    (hU : IsOpen U) (hUV : U ⊆ V) {v : H1Function V} {g : Vec d → ℝ}
    (hsol : IsWeakDivergenceFormH10SolutionOn b V v g 0)
    (hg : ∀ᵐ x ∂(volumeOn U), g x = 0) :
    IsWeakDivergenceFormSolutionOn b U (v.restrict hU hUV) 0 0 := by
  rw [DGNM.solutionOn_iff]
  intro φ
  have hsub : tsupport φ.toFun ⊆ V := φ.tsupport_subset.trans hUV
  obtain ⟨ht, heq⟩ := hsol (H10Function.ofContDiff hV φ.contDiff φ.hasCompactSupport hsub)
  have hflux : IntegrableOn (fun x => vecDot (matVecMul (b x) (v.grad x)) (φ.grad x)) V :=
    ht.flux_integrable
  refine ⟨by simpa only [H1Function.restrict_grad] using hflux.mono_set hUV, ?_⟩
  have hsrc : ∫ x in V, g x * φ x = 0 := by
    apply integral_eq_zero_of_ae
    have hg' : ∀ᵐ x ∂volume, x ∈ U → g x = 0 :=
      (ae_restrict_iff' hU.measurableSet).1 hg
    refine (ae_restrict_iff' hV.measurableSet).2 ?_
    filter_upwards [hg'] with x hx _
    by_cases hxU : x ∈ U
    · simp [hx hxU]
    · have : x ∉ tsupport φ.toFun := fun h => hxU (φ.tsupport_subset h)
      simp [image_eq_zero_of_notMem_tsupport this]
  have heq' : ∫ x in V, vecDot (matVecMul (b x) (v.grad x)) (φ.grad x) = 0 := by
    have h1 := heq
    simp only [H10Function.ofContDiff_toFun, Pi.zero_apply, vecDot_zero_left,
      integral_zero, sub_zero] at h1
    exact h1.trans hsrc
  rw [DGNM.setIntegral_vecDot_extendTest hV.measurableSet hUV] at heq'
  simpa only [H1Function.restrict_grad] using heq'

/-- De Giorgi's theorem on a ball `B_r(x₀) ⊆ U`: a continuous representative on `B_{r/2}(x₀)`
with a sup bound by the rescaled `L²` norm. -/
theorem exists_continuousOn_rep_ball (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Λ : ℝ}, 1 ≤ Λ → ∀ {U : Set (Vec d)}, IsOpen U →
      ∀ {b : CoeffField d}, (∀ i j : Fin d, AEMeasurable (fun x => b x i j) (volumeOn U)) →
      (∀ x ∈ U, IsEllipticMatrix 1 Λ (b x)) →
      ∀ {u : H1Function U}, IsWeakDivergenceFormSolutionOn b U u 0 0 →
      ∀ (x₀ : Vec d) {r : ℝ}, 0 < r → euclideanBall x₀ r ⊆ U →
      ∃ w : Vec d → ℝ, ContinuousOn w (euclideanBall x₀ (r / 2)) ∧
        w =ᵐ[volumeOn (euclideanBall x₀ (r / 2))] u.toFun ∧
        ∀ x ∈ euclideanBall x₀ (r / 2), ENNReal.ofReal |w x| ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            (ENNReal.ofReal ((r ^ d)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ r))) := by
  obtain ⟨CD, hCD, hDG⟩ := exists_deGiorgi_holder_constant d hd
  refine ⟨CD, hCD, ?_⟩
  intro Λ hΛ U hU b hmeas hell u hsol x₀ r hr hball
  obtain ⟨α, hα0, -, -, hDGa⟩ := hDG Λ hΛ
  obtain ⟨v, M₀, M₁, hae, -, hM₁, hvbd, hHold, hbound⟩ :=
    hDGa _ (DGNM.blowUpCoeff_aemeasurable hmeas x₀ hr hball)
      (DGNM.blowUpCoeff_elliptic hell x₀ hr hball) (DGNM.blowUp u x₀ hr hball)
      (DGNM.solutionOn_blowUp hU hsol x₀ hr hball)
  have hvc : ContinuousOn v (euclideanBall (0 : Vec d) (1 / 2)) :=
    DGNMAssembly.continuousOn_of_euclideanHolder hα0 hHold
  have hr2 : r * (1 / 2) = r / 2 := by ring
  have hmem : ∀ y ∈ euclideanBall x₀ (r / 2),
      r⁻¹ • (y - x₀) ∈ euclideanBall (0 : Vec d) (1 / 2) := by
    intro y hy
    rw [← DGNM.affineScale_mem_euclideanBall_iff x₀ hr, hr2]
    convert hy using 1
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]
  refine ⟨fun y => v (r⁻¹ • (y - x₀)), ?_, ?_, ?_⟩
  · exact hvc.comp (by fun_prop) hmem
  · have key := (DGNM.ae_comp_affineScale_ball_iff x₀ hr (1 / 2)
      (P := fun x => v (r⁻¹ • (x - x₀)) = u.toFun x)).1
    rw [hr2] at key
    apply key
    filter_upwards [hae] with y hy
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, hy]
    rfl
  · intro x hx
    have h1 : ENNReal.ofReal |v (r⁻¹ • (x - x₀))| ≤ ENNReal.ofReal (M₀ + M₁) :=
      ENNReal.ofReal_le_ofReal ((hvbd _ (hmem x hx)).trans (le_add_of_nonneg_right hM₁))
    refine h1.trans (hbound.trans (le_of_eq ?_))
    congr 1
    have := DGNM.eLpNorm_comp_affineScale_ball x₀ hr 1 u.toFun 2
    rw [mul_one] at this
    rw [← this]
    rfl

/-- **Pole lemma** (Lemma 4.38).  If `v ∈ H¹₀(B_R)` solves the adjoint equation with a
source vanishing a.e. in `B_ε`, then `v` has a representative continuous in `B_{ε/2}` bounded by
`C Λ^{d/4} ε^{-d/2} ‖v‖_{L²(B_R)}`. -/
theorem pole_continuousOn (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Λ R ε : ℝ}, 0 < ε → ε ≤ R → ∀ {a : CoeffField d},
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {g : Vec d → ℝ}, (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) →
      ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
        v.toH1Function g 0 →
      ∃ w : Vec d → ℝ, ContinuousOn w (euclideanBall (0 : Vec d) (ε / 2)) ∧
        w =ᵐ[volumeOn (euclideanBall (0 : Vec d) (ε / 2))] v.toH1Function.toFun ∧
        ∀ x ∈ euclideanBall (0 : Vec d) (ε / 2), ENNReal.ofReal |w x| ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            (ENNReal.ofReal ((ε ^ d)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
              eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R))) := by
  obtain ⟨C, hC, hball⟩ := exists_continuousOn_rep_ball hd
  refine ⟨C, hC, ?_⟩
  intro Λ R ε hε hεR a hmeas hell g hg v hv
  have hsub : euclideanBall (0 : Vec d) ε ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hε.le hεR
  have hΛ : 1 ≤ Λ :=
    one_le_of_elliptic ⟨0, center_mem_euclideanBall _ (hε.trans_le hεR)⟩ hell
  have hsol := solutionOn_of_source_ae_zero (isOpen_euclideanBall _ _) (isOpen_euclideanBall _ _)
    hsub hv hg
  obtain ⟨w, hwc, hwae, hwb⟩ := hball hΛ (isOpen_euclideanBall _ _)
    (fun i j => (aemeasurable_adjoint hmeas i j).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun x hx => elliptic_adjoint hell x (hsub hx)) hsol 0 hε subset_rfl
  refine ⟨w, hwc, hwae, fun x hx => (hwb x hx).trans ?_⟩
  gcongr
  exact eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)

/-- The constant of the pole lemma in real form: `K = C Λ^{d/4} ε^{-d/2} E`. -/
noncomputable def poleConst (C Λ ε E : ℝ) (d : ℕ) : ℝ :=
  C * Λ ^ ((d : ℝ) / 4) * ((ε ^ d)⁻¹) ^ (1 / 2 : ℝ) * E

theorem poleConst_nonneg {C Λ ε E : ℝ} (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hE : 0 ≤ E) :
    0 ≤ poleConst C Λ ε E d := by
  unfold poleConst
  have : 0 ≤ (ε ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg hε d)
  positivity

/-- **Pole lemma, averaged form.**  Under an energy bound `‖v‖₂ ≤ E ‖g‖₂`, the averages of `v`
over `B_ρ(0)` converge as `ρ → 0`, and are bounded by `K ‖g‖₂` for `ρ ≤ ε/2`, with
`K = poleConst C Λ ε E`. -/
theorem pole_average (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Λ R ε : ℝ}, 0 < ε → ε ≤ R → ∀ {a : CoeffField d},
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ {g : Vec d → ℝ}, MemL2On (euclideanBall (0 : Vec d) R) g →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) →
      ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
        v.toH1Function g 0 →
      ∀ {E : ℝ}, 0 ≤ E →
      eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≤
        ENNReal.ofReal E * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) →
      (∃ L : ℝ, Tendsto (fun ρ => integralAverage (euclideanBall (0 : Vec d) ρ)
          v.toH1Function.toFun) (𝓝[>] 0) (𝓝 L)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ε / 2 →
        |integralAverage (euclideanBall (0 : Vec d) ρ) v.toH1Function.toFun| ≤
          poleConst C Λ ε E d * (eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal := by
  obtain ⟨C, hC, hpole⟩ := pole_continuousOn (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro Λ R ε hε hεR a hmeas hell g hg2 hg v hv E hE hen
  have hΛ : 1 ≤ Λ :=
    one_le_of_elliptic ⟨0, center_mem_euclideanBall _ (hε.trans_le hεR)⟩ hell
  obtain ⟨w, hwc, hwae, hwb⟩ := hpole hε hεR hmeas hell hg v hv
  have hε2 : 0 < ε / 2 := half_pos hε
  have hgfin : eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≠ ⊤ := hg2.eLpNorm_ne_top
  -- the real bound on `w`
  have hK0 : 0 ≤ poleConst C Λ ε E d * (eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal
      :=
    mul_nonneg (poleConst_nonneg hC.le (by linarith) hε.le hE) ENNReal.toReal_nonneg
  have hbd : ∀ x ∈ euclideanBall (0 : Vec d) (ε / 2), |w x| ≤
      poleConst C Λ ε E d * (eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal := by
    intro x hx
    rw [← ENNReal.ofReal_le_ofReal_iff hK0]
    refine (hwb x hx).trans ?_
    have hinv : 0 ≤ (ε ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg hε.le d)
    have hhalf : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
    rw [hhalf]
    calc ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((ε ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)))
        ≤ ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
          (ENNReal.ofReal ((ε ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal E * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R)))) := by
          gcongr
      _ = ENNReal.ofReal (poleConst C Λ ε E d *
            (eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hinv (by norm_num)]
          conv_lhs => rw [← ENNReal.ofReal_toReal hgfin]
          have h1 : 0 ≤ ((ε ^ d)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hinv _
          have h2 : 0 ≤ C * Λ ^ ((d : ℝ) / 4) :=
            mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
          rw [← ENNReal.ofReal_mul hE, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
          congr 1
          unfold poleConst
          ring
  have havg : ∀ ρ, 0 < ρ → ρ ≤ ε / 2 →
      integralAverage (euclideanBall (0 : Vec d) ρ) v.toH1Function.toFun =
        integralAverage (euclideanBall (0 : Vec d) ρ) w := fun ρ hρ hρε =>
    integralAverage_congr_ae (euclideanBall_mono hρ.le hρε) hwae.symm
  refine ⟨⟨w 0, ?_⟩, fun ρ hρ hρε => ?_⟩
  · refine (tendsto_integralAverage_euclideanBall hε2 hwc).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε2] with ρ hρ
    exact (havg ρ hρ.1 hρ.2.le).symm
  · rw [havg ρ hρ hρε]
    exact abs_integralAverage_le_of_abs_le hρ hρε hbd

end PDE.Ch4Green
