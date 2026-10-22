module

public import PDEFoundation.Analysis.RieszWeakType

/-! # Weak-type bound for the Riesz potential: the Chebyshev argument

Near/far splitting of the kernel at radius `δ = (2 ‖f‖₁ / λ)^(1/(d-1))`, Fubini for the near
part, and Chebyshev's inequality. -/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Near part of the kernel: the kernel restricted to the ball of radius `δ`. -/
private def nearKernel (d : ℕ) (δ : ℝ) (z : Vec d) : ℝ≥0∞ :=
  (euclideanBall (0 : Vec d) δ).indicator (fun z => ENNReal.ofReal (rieszKernelOne d z)) z

/-- Far part of the kernel. -/
private def farKernel (d : ℕ) (δ : ℝ) (z : Vec d) : ℝ≥0∞ :=
  (euclideanBall (0 : Vec d) δ)ᶜ.indicator (fun z => ENNReal.ofReal (rieszKernelOne d z)) z

private theorem measurable_nearKernel (δ : ℝ) : Measurable (nearKernel d δ) :=
  (measurable_rieszKernelOne.ennreal_ofReal).indicator
    (isOpen_euclideanBall _ _).measurableSet

private theorem near_add_far (δ : ℝ) (z : Vec d) :
    ENNReal.ofReal (rieszKernelOne d z) = nearKernel d δ z + farKernel d δ z := by
  simp only [nearKernel, farKernel]
  exact (congrFun (indicator_self_add_compl (euclideanBall (0 : Vec d) δ)
    (fun z => ENNReal.ofReal (rieszKernelOne d z))) z).symm

private theorem farKernel_le {δ : ℝ} (hd : 2 ≤ d) (hδ : 0 < δ) (z : Vec d) :
    farKernel d δ z ≤ ENNReal.ofReal (δ ^ ((1 : ℝ) - d)) := by
  by_cases hz : z ∈ (euclideanBall (0 : Vec d) δ)ᶜ
  · simp only [farKernel, indicator_of_mem hz]
    apply ENNReal.ofReal_le_ofReal
    apply rieszKernelOne_le_of_le hd hδ
    have : ¬ vecEuclideanNorm (z - 0) < δ := by
      rwa [mem_compl_iff, mem_euclideanBall_iff_vecEuclideanNorm_lt hδ] at hz
    simpa using not_lt.mp this
  · simp [farKernel, indicator_of_notMem hz]

/-- The near part of the potential has integral `d |B₁| δ ‖f‖₁`. -/
private theorem lintegral_near_potential (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) {f : Vec d → ℝ}
    (hf : AEMeasurable f) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f y) * nearKernel d δ (x - y) =
      (∫⁻ y, ENNReal.ofReal (f y)) *
        ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * δ) := by
  have hmeas : AEMeasurable (Function.uncurry fun x y : Vec d =>
      ENNReal.ofReal (f y) * nearKernel d δ (x - y)) (volume.prod volume) := by
    have h1 : AEMeasurable (fun q : Vec d × Vec d => ENNReal.ofReal (f q.2))
        (volume.prod volume) :=
      (hf.ennreal_ofReal).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable (fun q : Vec d × Vec d => nearKernel d δ (q.1 - q.2)) :=
      (measurable_nearKernel δ).comp (measurable_fst.sub measurable_snd)
    exact h1.mul h2.aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  have hinner : ∀ y : Vec d, ∫⁻ x, ENNReal.ofReal (f y) * nearKernel d δ (x - y) =
      ENNReal.ofReal (f y) *
        ENNReal.ofReal ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * δ) := by
    intro y
    rw [lintegral_const_mul _ (f := fun x => nearKernel d δ (x - y))
      ((measurable_nearKernel δ).comp (measurable_id.sub_const y))]
    congr 1
    rw [lintegral_sub_right_eq_self (μ := (volume : Measure (Vec d))) (nearKernel d δ) y]
    unfold nearKernel
    rw [lintegral_indicator (isOpen_euclideanBall _ _).measurableSet,
      lintegral_euclideanBall_rieszKernelOne hd hδ]
  simp_rw [hinner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]

private theorem aemeasurable_near_integrand (δ : ℝ) {f : Vec d → ℝ} (hf : AEMeasurable f) :
    AEMeasurable (fun q : Vec d × Vec d =>
      ENNReal.ofReal (f q.2) * nearKernel d δ (q.1 - q.2)) (volume.prod volume) :=
  ((hf.ennreal_ofReal).comp_quasiMeasurePreserving
    Measure.quasiMeasurePreserving_snd).mul
    ((measurable_nearKernel δ).comp (measurable_fst.sub measurable_snd)).aemeasurable

/-- Exponent identity: `2 (A/λ) δ = (2A/λ)^(d/(d-1))` for `δ = (2A/λ)^(1/(d-1))`. -/
private theorem two_mul_div_mul_delta {A l : ℝ} (hd : 2 ≤ d) (hA : 0 < A) (hl : 0 < l) :
    2 * (A / l) * (2 * A / l) ^ (1 / ((d : ℝ) - 1)) =
      2 ^ ((d : ℝ) / (d - 1)) * (A / l) ^ ((d : ℝ) / (d - 1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hne : (d : ℝ) - 1 ≠ 0 := by linarith
  have hexp : (d : ℝ) / (d - 1) = 1 + 1 / ((d : ℝ) - 1) := by
    field_simp; ring
  have hpos : 0 < 2 * A / l := by positivity
  have hb : 2 * (A / l) = 2 * A / l := by ring
  rw [hexp, ← Real.mul_rpow (by norm_num) (by positivity), hb, Real.rpow_add hpos,
    Real.rpow_one]

/-- **Weak-type bound for the Riesz potential, extended-valued form.**  For `d ≥ 2`,
nonnegative integrable `f` and `λ > 0`,
`|{I₁ f ≥ λ}| ≤ 2^{d/(d-1)} d |B₁| (‖f‖₁ / λ)^{d/(d-1)}`. -/
theorem volume_setOf_le_rieszLIntegralOne (hd : 2 ≤ d) {f : Vec d → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f) {l : ℝ} (hl : 0 < l) :
    volume {x | ENNReal.ofReal l ≤ rieszLIntegralOne f x} ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / (d - 1)) * d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal *
        ((∫ y, f y) / l) ^ ((d : ℝ) / (d - 1))) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set A : ℝ := ∫ y, f y with hAdef
  have hA0 : 0 ≤ A := integral_nonneg hf0
  have hAl : ∫⁻ y, ENNReal.ofReal (f y) = ENNReal.ofReal A :=
    (ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)).symm
  set B : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hBdef
  rcases hA0.eq_or_lt with hA | hA
  · -- `f = 0` almost everywhere, so the potential vanishes
    have hz : ∀ x, rieszLIntegralOne f x = 0 := by
      intro x
      have hae : (fun y => ENNReal.ofReal (f y)) =ᵐ[volume] 0 := by
        have := (lintegral_eq_zero_iff' hf.aemeasurable.ennreal_ofReal).mp
          (by rw [hAl, ← hA]; simp)
        exact this
      unfold rieszLIntegralOne
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hae] with y hy
        simp [hy]
    have : {x | ENNReal.ofReal l ≤ rieszLIntegralOne f x} = ∅ := by
      ext x
      simp [hz x, hl]
    rw [this]; simp
  · set δ : ℝ := (2 * A / l) ^ (1 / ((d : ℝ) - 1)) with hδdef
    have hpos : 0 < 2 * A / l := by positivity
    have hδ : 0 < δ := Real.rpow_pos_of_pos hpos _
    have hδpow : δ ^ ((1 : ℝ) - d) = l / (2 * A) := by
      rw [hδdef, ← Real.rpow_mul hpos.le]
      have hne : (d : ℝ) - 1 ≠ 0 := by linarith
      have : 1 / ((d : ℝ) - 1) * (1 - d) = -1 := by
        field_simp
        ring
      rw [this, Real.rpow_neg_one, inv_div]
    have hfar : ENNReal.ofReal A * ENNReal.ofReal (δ ^ ((1 : ℝ) - d)) =
        ENNReal.ofReal (l / 2) := by
      rw [← ENNReal.ofReal_mul hA0, hδpow]
      congr 1; field_simp
    -- pointwise splitting
    have hsplit : ∀ x, rieszLIntegralOne f x =
        (∫⁻ y, ENNReal.ofReal (f y) * nearKernel d δ (x - y)) +
        ∫⁻ y, ENNReal.ofReal (f y) * farKernel d δ (x - y) := by
      intro x
      unfold rieszLIntegralOne
      rw [← lintegral_add_left']
      · refine lintegral_congr fun y => ?_
        rw [mul_comm, near_add_far δ (x - y), mul_add]
      · exact (hf.aemeasurable.ennreal_ofReal.mul
          ((measurable_nearKernel δ).comp (measurable_const.sub measurable_id)).aemeasurable)
    have hfarle : ∀ x, ∫⁻ y, ENNReal.ofReal (f y) * farKernel d δ (x - y) ≤
        ENNReal.ofReal (l / 2) := by
      intro x
      calc ∫⁻ y, ENNReal.ofReal (f y) * farKernel d δ (x - y)
          ≤ ∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (δ ^ ((1 : ℝ) - d)) :=
            lintegral_mono fun y => mul_le_mul' le_rfl (farKernel_le hd hδ _)
        _ = ENNReal.ofReal (l / 2) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hAl, hfar]
    set N : Vec d → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (f y) * nearKernel d δ (x - y)
      with hN
    have hsub : {x | ENNReal.ofReal l ≤ rieszLIntegralOne f x} ⊆
        {x | ENNReal.ofReal (l / 2) ≤ N x} := by
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hsplit x] at hx
      have h2 : ENNReal.ofReal l = ENNReal.ofReal (l / 2) + ENNReal.ofReal (l / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      have : ENNReal.ofReal (l / 2) + ENNReal.ofReal (l / 2) ≤
          ENNReal.ofReal (l / 2) + N x := by
        rw [← h2, add_comm]
        exact hx.trans (add_le_add_right (hfarle x) _)
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp this
    have hNae : AEMeasurable N volume := by
      have := (aemeasurable_near_integrand δ hf.aemeasurable).lintegral_prod_right'
      exact this
    have hcheb := mul_meas_ge_le_lintegral₀ hNae (ENNReal.ofReal (l / 2))
    have hNint : ∫⁻ x, N x = ENNReal.ofReal A * ENNReal.ofReal (d * B * δ) := by
      rw [hN, lintegral_near_potential hd hδ hf.aemeasurable, hAl]
    rw [hNint] at hcheb
    have hcheb' : ENNReal.ofReal (l / 2) * volume {x | ENNReal.ofReal l ≤ rieszLIntegralOne f x}
        ≤ ENNReal.ofReal (A * (d * B * δ)) := by
      rw [ENNReal.ofReal_mul hA0]
      exact (mul_le_mul' le_rfl (measure_mono hsub)).trans hcheb
    have h1 : ENNReal.ofReal (2 / l) * ENNReal.ofReal (l / 2) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : 2 / l * (l / 2) = 1 := by field_simp
      rw [this, ENNReal.ofReal_one]
    calc volume {x | ENNReal.ofReal l ≤ rieszLIntegralOne f x}
        = ENNReal.ofReal (2 / l) * (ENNReal.ofReal (l / 2) *
            volume {x | ENNReal.ofReal l ≤ rieszLIntegralOne f x}) := by
          rw [← mul_assoc, h1, one_mul]
      _ ≤ ENNReal.ofReal (2 / l) * ENNReal.ofReal (A * (d * B * δ)) :=
          mul_le_mul' le_rfl hcheb'
      _ = ENNReal.ofReal (2 / l * (A * (d * B * δ))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = _ := by
          congr 1
          have := two_mul_div_mul_delta hd hA hl
          rw [← hδdef] at this
          calc 2 / l * (A * (d * B * δ)) = (d * B) * (2 * (A / l) * δ) := by ring
            _ = _ := by rw [this]; ring

/-- **Weak-type bound for the Riesz potential** `I₁` (Bochner form), Lemma 1.8. -/
theorem volume_setOf_le_rieszPotentialOne (hd : 2 ≤ d) {f : Vec d → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f) {l : ℝ} (hl : 0 < l) :
    volume {x | l ≤ rieszPotentialOne f x} ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / (d - 1)) * d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal *
        ((∫ y, f y) / l) ^ ((d : ℝ) / (d - 1))) := by
  refine le_trans (measure_mono ?_) (volume_setOf_le_rieszLIntegralOne hd hf0 hf hl)
  intro x hx
  simp only [mem_ofPred_eq] at hx ⊢
  have hint : Integrable (fun y => rieszKernelOne d (x - y) * f y) := by
    by_contra h
    unfold rieszPotentialOne at hx
    rw [integral_undef h] at hx
    linarith
  unfold rieszLIntegralOne
  have hnn : 0 ≤ᵐ[volume] fun y => rieszKernelOne d (x - y) * f y :=
    Filter.Eventually.of_forall fun y => mul_nonneg (rieszKernelOne_nonneg _) (hf0 y)
  have := ofReal_integral_eq_lintegral_ofReal hint hnn
  calc ENNReal.ofReal l ≤ ENNReal.ofReal (rieszPotentialOne f x) := ENNReal.ofReal_le_ofReal hx
    _ = _ := by
      unfold rieszPotentialOne
      rw [this]
      refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_mul (rieszKernelOne_nonneg _)]

end

end PDE
