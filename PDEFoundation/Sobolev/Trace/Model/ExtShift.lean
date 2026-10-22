module

public import PDEFoundation.Sobolev.Trace.Model.ExtBoundary

/-!
# Upward shifts of the extension converge in `W^{1,p}` of the half-space

The function `E g` and its partial derivatives belong to `L^p` of the half-space (by the energy
bound), and translations are continuous in `L^p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ}

/-- Lebesgue measure on the model space is an additive Haar measure. -/
instance instIsAddHaarMeasureVolumeModel (n : ℕ) :
    (volume : Measure (Vec n × ℝ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume : Measure (Vec n)).prod (volume : Measure ℝ)).IsAddHaarMeasure

theorem abs_tanGrad_le_modelGradNorm (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) (i : Fin n) :
    |tanGrad v z i| ≤ modelGradNorm v z := by
  unfold modelGradNorm
  refine (abs_apply_le_vecEuclideanNorm (tanGrad v z) i).trans ?_
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (normDeriv v z)])

theorem abs_normDeriv_le_modelGradNorm (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) :
    |normDeriv v z| ≤ modelGradNorm v z := by
  unfold modelGradNorm
  exact Real.abs_le_sqrt (by nlinarith [vecNormSq_nonneg (tanGrad v z)])

theorem memLp_indicator_upperHalf {p : ℝ} (hp : 0 < p) {f : Vec n × ℝ → ℝ}
    (hf : ContinuousOn f (upperHalf n))
    (hint : ∫⁻ z in upperHalf n, ENNReal.ofReal (|f z| ^ p) < ⊤) :
    MemLp ((upperHalf n).indicator f) (ENNReal.ofReal p) volume := by
  have hs : MeasurableSet (upperHalf n) := (isOpen_upperHalf n).measurableSet
  have hmeas : AEStronglyMeasurable ((upperHalf n).indicator f) volume :=
    (aestronglyMeasurable_indicator_iff hs).2 (hf.aestronglyMeasurable hs)
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top hmeas, ENNReal.toReal_ofReal hp.le]
  have : ∀ z, ‖(upperHalf n).indicator f z‖ₑ ^ p =
      (upperHalf n).indicator (fun z => ENNReal.ofReal (|f z| ^ p)) z := by
    intro z
    by_cases hz : z ∈ upperHalf n
    · simp only [Set.indicator_of_mem hz]
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
    · simp [Set.indicator_of_notMem hz, ENNReal.zero_rpow_of_pos hp]
  simp_rw [this]
  rwa [lintegral_indicator hs]

theorem lintegral_ofReal_abs_rpow_lt_top {p : ℝ} (hp : 0 < p) {g : Vec n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume) : ∫⁻ x, ENNReal.ofReal (|g x| ^ p) < ⊤ := by
  have h := hg
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le] at h
  refine lt_of_eq_of_lt ?_ h
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

theorem lintegral_modelExt_lt_top {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume)
    (hfin : flatGagliardo n ((n : ℝ) + p - 1) p g ≠ ⊤) :
    ∫⁻ z in upperHalf n, (ENNReal.ofReal (|modelExt n g z| ^ p) +
      ENNReal.ofReal (modelGradNorm (modelExt n g) z ^ p)) < ⊤ := by
  obtain ⟨C, hC⟩ := modelExt_bound (p := p) n hp
  refine (hC g hg).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
  exact ENNReal.add_lt_top.2 ⟨lintegral_ofReal_abs_rpow_lt_top (by linarith) hg, hfin.lt_top⟩

theorem aemeasurable_translate_diff {p : ℝ} {F : Vec n × ℝ → ℝ}
    (hF : AEStronglyMeasurable F volume) (v : Vec n × ℝ) :
    AEMeasurable (fun z => ENNReal.ofReal (|F (z + v) - F z| ^ p)) volume := by
  have h1 : AEStronglyMeasurable (fun z => F (z + v) - F z) volume :=
    (hF.comp_measurePreserving (measurePreserving_add_right volume v)).sub hF
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    ((continuous_abs.comp_aestronglyMeasurable h1).aemeasurable.pow_const p)

theorem upperHalf_add_vertical {n : ℕ} {z : Vec n × ℝ} (hz : z ∈ upperHalf n) {τ : ℝ} (hτ : 0 < τ) :
    z + ((0 : Vec n), τ) ∈ upperHalf n ∧ z + ((0 : Vec n), τ) = (z.1, z.2 + τ) := by
  refine ⟨?_, by ext <;> simp⟩
  rw [mem_upperHalf] at hz ⊢
  simp only [Prod.snd_add]
  linarith

theorem shift_pointwise {p : ℝ} (hp : 1 < p) (E : Vec n × ℝ → ℝ) {z : Vec n × ℝ}
    (hz : z ∈ upperHalf n) {τ : ℝ} (hτ : 0 < τ) :
    ENNReal.ofReal (|E (z.1, z.2 + τ) - E z| ^ p) +
        ENNReal.ofReal (|normDeriv E (z.1, z.2 + τ) - normDeriv E z| ^ p) +
        ENNReal.ofReal (vecEuclideanNorm (tanGrad E (z.1, z.2 + τ) - tanGrad E z) ^ p) ≤
      ENNReal.ofReal (|(upperHalf n).indicator E (z + ((0 : Vec n), τ)) -
          (upperHalf n).indicator E z| ^ p) +
        ENNReal.ofReal (|(upperHalf n).indicator (normDeriv E) (z + ((0 : Vec n), τ)) -
          (upperHalf n).indicator (normDeriv E) z| ^ p) +
        ENNReal.ofReal ((n : ℝ) ^ (p - 1)) * ∑ i : Fin n,
          ENNReal.ofReal (|(upperHalf n).indicator (fun z => tanGrad E z i) (z + ((0 : Vec n), τ)) -
            (upperHalf n).indicator (fun z => tanGrad E z i) z| ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨hmem, heq⟩ := upperHalf_add_vertical hz hτ
  simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hz]
  rw [heq]
  refine add_le_add (add_le_add le_rfl le_rfl) ?_
  -- the vector term
  set Δ : Vec n := tanGrad E (z.1, z.2 + τ) - tanGrad E z with hΔ
  have h1 : vecEuclideanNorm Δ ^ p ≤ (∑ i : Fin n, |Δ i|) ^ p :=
    Real.rpow_le_rpow (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_le_sum_abs Δ) hp0
  have h2 := Real.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset (Fin n)) (fun i => Δ i) hp.le
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have hsum : 0 ≤ ∑ i : Fin n, |Δ i| ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  calc ENNReal.ofReal (vecEuclideanNorm Δ ^ p)
      ≤ ENNReal.ofReal ((n : ℝ) ^ (p - 1) * ∑ i : Fin n, |Δ i| ^ p) :=
        ENNReal.ofReal_le_ofReal (h1.trans h2)
    _ = ENNReal.ofReal ((n : ℝ) ^ (p - 1)) * ∑ i : Fin n, ENNReal.ofReal (|Δ i| ^ p) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)]
    _ = _ := by
        simp only [hΔ, Pi.sub_apply]

/-- Upward shifts converge in `W^{1,p}` of the half-space. -/
theorem modelExt_tendsto_shift {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume)
    (hfin : flatGagliardo n ((n : ℝ) + p - 1) p g ≠ ⊤) :
    Tendsto (fun τ : ℝ => ∫⁻ z in upperHalf n,
        (ENNReal.ofReal (|modelExt n g (z.1, z.2 + τ) - modelExt n g z| ^ p) +
          ENNReal.ofReal (|normDeriv (modelExt n g) (z.1, z.2 + τ) -
            normDeriv (modelExt n g) z| ^ p) +
          ENNReal.ofReal (vecEuclideanNorm (tanGrad (modelExt n g) (z.1, z.2 + τ) -
            tanGrad (modelExt n g) z) ^ p)))
      (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hq : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  have hloc := hg.locallyIntegrable hq
  have hE := contDiffOn_modelExt hloc
  have hfd := hE.continuousOn_fderiv_of_isOpen (isOpen_upperHalf n) le_rfl
  have htot := lintegral_modelExt_lt_top hp hg hfin
  have hint0 : ∫⁻ z in upperHalf n, ENNReal.ofReal (|modelExt n g z| ^ p) < ⊤ :=
    (lintegral_mono fun z => le_self_add).trans_lt htot
  have hintm : ∫⁻ z in upperHalf n, ENNReal.ofReal (modelGradNorm (modelExt n g) z ^ p) < ⊤ :=
    (lintegral_mono fun z => le_add_self).trans_lt htot
  have hcont_nd : ContinuousOn (normDeriv (modelExt n g)) (upperHalf n) :=
    hfd.clm_apply continuousOn_const
  have hcont_tan : ∀ i : Fin n, ContinuousOn (fun z => tanGrad (modelExt n g) z i) (upperHalf n) :=
    fun i => hfd.clm_apply continuousOn_const
  have hintnd : ∫⁻ z in upperHalf n,
      ENNReal.ofReal (|normDeriv (modelExt n g) z| ^ p) < ⊤ :=
    (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _)
      (abs_normDeriv_le_modelGradNorm _ z) hp0.le)).trans_lt hintm
  have hinti : ∀ i : Fin n, ∫⁻ z in upperHalf n,
      ENNReal.ofReal (|tanGrad (modelExt n g) z i| ^ p) < ⊤ := fun i =>
    (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _)
      (abs_tanGrad_le_modelGradNorm _ z i) hp0.le)).trans_lt hintm
  have hU0 := memLp_indicator_upperHalf hp0 hE.continuousOn hint0
  have hUn := memLp_indicator_upperHalf hp0 hcont_nd hintnd
  have hUi := fun i : Fin n => memLp_indicator_upperHalf hp0 (hcont_tan i) (hinti i)
  have hv : Tendsto (fun τ : ℝ => ((0 : Vec n), τ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun τ : ℝ => ((0 : Vec n), τ)) (𝓝 0) (𝓝 ((0 : Vec n), (0 : ℝ))) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact (show ((0 : Vec n), (0 : ℝ)) = 0 from rfl) ▸ this.mono_left nhdsWithin_le_nhds
  have T0 := (tendsto_lintegral_translate (volume : Measure (Vec n × ℝ)) hp.le hU0).comp hv
  have Tn := (tendsto_lintegral_translate (volume : Measure (Vec n × ℝ)) hp.le hUn).comp hv
  have Ti := fun i : Fin n =>
    (tendsto_lintegral_translate (volume : Measure (Vec n × ℝ)) hp.le (hUi i)).comp hv
  have hup : Tendsto (fun τ : ℝ =>
      (∫⁻ z, ENNReal.ofReal (|(upperHalf n).indicator (modelExt n g) (z + ((0 : Vec n), τ)) -
          (upperHalf n).indicator (modelExt n g) z| ^ p)) +
        (∫⁻ z, ENNReal.ofReal (|(upperHalf n).indicator (normDeriv (modelExt n g))
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator (normDeriv (modelExt n g)) z| ^ p)) +
        ENNReal.ofReal ((n : ℝ) ^ (p - 1)) * ∑ i : Fin n,
          ∫⁻ z, ENNReal.ofReal (|(upperHalf n).indicator (fun z => tanGrad (modelExt n g) z i)
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator
              (fun z => tanGrad (modelExt n g) z i) z| ^ p))
      (𝓝[>] 0) (𝓝 0) := by
    have hsum : Tendsto (fun τ : ℝ => ∑ i : Fin n,
        ∫⁻ z, ENNReal.ofReal (|(upperHalf n).indicator (fun z => tanGrad (modelExt n g) z i)
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator
              (fun z => tanGrad (modelExt n g) z i) z| ^ p)) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => Ti i
      simpa using this
    have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((n : ℝ) ^ (p - 1))) hsum
      (Or.inr ENNReal.ofReal_ne_top)
    have h4 := (T0.add Tn).add h3
    simpa using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun τ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : 0 < τ := hτ
  have hs : MeasurableSet (upperHalf n) := (isOpen_upperHalf n).measurableSet
  calc ∫⁻ z in upperHalf n, _ ≤ ∫⁻ z in upperHalf n,
        (ENNReal.ofReal (|(upperHalf n).indicator (modelExt n g) (z + ((0 : Vec n), τ)) -
          (upperHalf n).indicator (modelExt n g) z| ^ p) +
        ENNReal.ofReal (|(upperHalf n).indicator (normDeriv (modelExt n g))
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator (normDeriv (modelExt n g)) z| ^ p) +
        ENNReal.ofReal ((n : ℝ) ^ (p - 1)) * ∑ i : Fin n,
          ENNReal.ofReal (|(upperHalf n).indicator (fun z => tanGrad (modelExt n g) z i)
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator
              (fun z => tanGrad (modelExt n g) z i) z| ^ p)) :=
        setLIntegral_mono' hs fun z hz => shift_pointwise hp (modelExt n g) hz hτ0
    _ ≤ ∫⁻ z,
        (ENNReal.ofReal (|(upperHalf n).indicator (modelExt n g) (z + ((0 : Vec n), τ)) -
          (upperHalf n).indicator (modelExt n g) z| ^ p) +
        ENNReal.ofReal (|(upperHalf n).indicator (normDeriv (modelExt n g))
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator (normDeriv (modelExt n g)) z| ^ p) +
        ENNReal.ofReal ((n : ℝ) ^ (p - 1)) * ∑ i : Fin n,
          ENNReal.ofReal (|(upperHalf n).indicator (fun z => tanGrad (modelExt n g) z i)
            (z + ((0 : Vec n), τ)) - (upperHalf n).indicator
              (fun z => tanGrad (modelExt n g) z i) z| ^ p)) := setLIntegral_le_lintegral _ _
    _ = _ := by
        have m0 := aemeasurable_translate_diff (p := p) hU0.aestronglyMeasurable ((0 : Vec n), τ)
        have mn := aemeasurable_translate_diff (p := p) hUn.aestronglyMeasurable ((0 : Vec n), τ)
        have mi := fun i : Fin n =>
          aemeasurable_translate_diff (p := p) (hUi i).aestronglyMeasurable ((0 : Vec n), τ)
        have mA : AEMeasurable (fun z => ENNReal.ofReal
            (|(upperHalf n).indicator (modelExt n g) (z + ((0 : Vec n), τ)) -
              (upperHalf n).indicator (modelExt n g) z| ^ p) +
            ENNReal.ofReal (|(upperHalf n).indicator (normDeriv (modelExt n g))
              (z + ((0 : Vec n), τ)) - (upperHalf n).indicator (normDeriv (modelExt n g)) z| ^ p))
            volume := m0.add mn
        have mS : AEMeasurable (fun z => ∑ i : Fin n, ENNReal.ofReal
            (|(upperHalf n).indicator (fun z => tanGrad (modelExt n g) z i)
              (z + ((0 : Vec n), τ)) - (upperHalf n).indicator
                (fun z => tanGrad (modelExt n g) z i) z| ^ p)) volume :=
          Finset.aemeasurable_fun_sum _ fun i _ => mi i
        rw [lintegral_add_left' mA, lintegral_add_left' m0, lintegral_const_mul'' _ mS,
          lintegral_finsetSum' _ fun i _ => mi i]

end PDE.TraceLane
