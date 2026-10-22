module

public import EllipticRegularity.Parabolic.Energy.Slab
public import EllipticRegularity.Parabolic.Moser.TimeContinuity

/-!
# Order transfer to every interior time slice

The parabolic energy space stores weak continuity only after pairing with a
compactly supported spatial `L²` function.  This module turns an almost
everywhere space-time upper bound into an every-interior-time bound for each
nonnegative such pairing.  The usual order-duality argument then gives the
corresponding spatial essential bound.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.Moser

private noncomputable def negParH1Function
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (u : ParH1Function U I) : ParH1Function U I where
  toFun := fun z => -u.toFun z
  grad := fun z => -u.grad z
  memL2 := u.memL2.neg
  gradMemL2 := by
    intro i
    change MemLp (fun z => -(u.grad z i)) 2 (volume.restrict (U ×ˢ I))
    exact (u.gradMemL2 i).neg
  sliceWeakGradient := by
    filter_upwards [u.sliceWeakGradient] with t ht
    intro i φ hφ hcompact hsub
    have h := ht i φ hφ hcompact hsub
    simp only [parSlice, Pi.neg_apply, neg_mul, integral_neg] at h ⊢
    linarith
  sliceL2loc := by
    intro t ht K hK hKU
    change MemLp (fun x => -u.toFun (x, t)) 2 (volume.restrict K)
    exact (u.sliceL2loc t ht K hK hKU).neg
  weakCont := by
    intro ψ hψ
    have hcont := u.weakCont ψ hψ
    have hneg : (fun t => ∫ x in U, -u.toFun (x, t) * ψ x) =
        fun t => -(∫ x in U, u.toFun (x, t) * ψ x) := by
      funext t
      rw [show (fun x => -u.toFun (x, t) * ψ x) =
        fun x => -(u.toFun (x, t) * ψ x) by funext x; ring, integral_neg]
    rw [hneg]
    exact hcont.neg

/-- A space-time almost-everywhere upper bound controls every nonnegative
compactly supported `L²` pairing at almost every time. -/
theorem ae_parH1_pairing_le_of_ae_spaceTime_le
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I) {M : ℝ}
    (hbound : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), u.toFun z ≤ M)
    {ψ : Vec d → ℝ} (hψ : IsL2c U ψ)
    (hψnonneg : ∀ x, 0 ≤ ψ x) :
    ∀ᵐ t ∂(volume.restrict I),
      (∫ x in U, u.toFun (x, t) * ψ x) ≤
        M * (∫ x in U, ψ x) := by
  have hprod : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict I)),
      u.toFun z ≤ M := by
    rw [← PDE.Parabolic.Energy.volume_restrict_prod U I]
    exact hbound
  have hsections := PDE.Parabolic.Energy.ae_ae_swap hprod
  filter_upwards [hsections, ae_restrict_mem hImeas] with t ht htI
  have hf : IntegrableOn (fun x => u.toFun (x, t) * ψ x) U := by
    obtain ⟨K, hK, hKU, hψzero⟩ := hψ.2
    have hslice := u.sliceL2loc t htI K hK hKU
    have hψK : MemL2On K ψ :=
      hψ.1.mono_measure (Measure.restrict_mono hKU le_rfl)
    have hprodK : IntegrableOn (fun x => u.toFun (x, t) * ψ x) K :=
      integrableOn_mul_of_memL2On hslice hψK
    have hsupport : Function.support (fun x => u.toFun (x, t) * ψ x) ⊆ K := by
      apply Function.support_subset_iff'.2
      intro x hxK
      simp [hψzero x hxK]
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hprodK |>.integrableOn
  have hg : IntegrableOn (fun x => M * ψ x) U := by
    obtain ⟨K, hK, hKU, hψzero⟩ := hψ.2
    have hψK : MemL2On K ψ :=
      hψ.1.mono_measure (Measure.restrict_mono hKU le_rfl)
    have hψintK : IntegrableOn ψ K := by
      let : IsFiniteMeasure (volumeOn K) := ⟨by
        rw [volumeOn, Measure.restrict_apply MeasurableSet.univ]
        simpa [volumeOn, Measure.restrict_apply MeasurableSet.univ] using
          hK.measure_lt_top⟩
      exact hψK.integrable (by norm_num)
    have hmulK : IntegrableOn (fun x => M * ψ x) K := hψintK.const_mul M
    have hsupport : Function.support (fun x => M * ψ x) ⊆ K := by
      apply Function.support_subset_iff'.2
      intro x hxK
      simp [hψzero x hxK]
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hmulK |>.integrableOn
  have hle : ∀ᵐ x ∂(volumeOn U),
      u.toFun (x, t) * ψ x ≤ M * ψ x :=
    ht.mono fun x hx => mul_le_mul_of_nonneg_right hx (hψnonneg x)
  calc
    _ = ∫ x in U, u.toFun (x, t) * ψ x ∂volume := rfl
    _ ≤ ∫ x in U, M * ψ x ∂volume := integral_mono_ae hf hg hle
    _ = M * (∫ x in U, ψ x) := by rw [integral_const_mul]

/-- Weak continuity upgrades the preceding almost-every-time pairing estimate
to every time in the interior of the time interval. -/
theorem parH1_pairing_le_at_every_interior_time
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (u : ParH1Function U I) {M : ℝ} {ψ : Vec d → ℝ}
    (hψ : IsL2c U ψ)
    (hae : ∀ᵐ t ∂(volume.restrict I),
      (∫ x in U, u.toFun (x, t) * ψ x) ≤ M * (∫ x in U, ψ x)) :
    ∀ t ∈ interior I,
      (∫ x in U, u.toFun (x, t) * ψ x) ≤ M * (∫ x in U, ψ x) := by
  let f : ℝ → ℝ := fun t =>
    (∫ x in U, u.toFun (x, t) * ψ x) - M * (∫ x in U, ψ x)
  have hfcont : ContinuousOn f (interior I) := by
    have hcont := u.weakCont ψ hψ
    have hsub : ContinuousOn
        (fun t => ∫ x in U, u.toFun (x, t) * ψ x) (interior I) :=
      hcont.mono interior_subset
    change ContinuousOn
      ((fun t => ∫ x in U, u.toFun (x, t) * ψ x) -
        (fun _ => M * (∫ x in U, ψ x))) (interior I)
    exact hsub.sub continuousOn_const
  have hIae : ∀ᵐ t ∂(volume.restrict (interior I)), f t ≤ 0 := by
    have hrestrict := ae_restrict_of_ae_restrict_of_subset
      (interior_subset : interior I ⊆ I) hae
    filter_upwards [hrestrict] with t ht
    simp only [f]
    linarith
  have hle := continuousOn_le_of_ae_restrict_le isOpen_interior hfcont
    (M := 0) hIae
  intro t ht
  have := hle t ht
  simpa [f] using this

/-- **Final time-slice order transfer.** A space-time a.e. upper bound for a
parabolic `H¹` function yields the same upper bound for every nonnegative
compactly supported `L²` pairing at each interior time. -/
theorem parH1_pairing_le_at_every_interior_time_of_ae_spaceTime_le
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I) {M : ℝ}
    (hbound : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), u.toFun z ≤ M)
    {ψ : Vec d → ℝ} (hψ : IsL2c U ψ)
    (hψnonneg : ∀ x, 0 ≤ ψ x) :
    ∀ t ∈ interior I,
      (∫ x in U, u.toFun (x, t) * ψ x) ≤ M * (∫ x in U, ψ x) := by
  apply parH1_pairing_le_at_every_interior_time u hψ
  exact ae_parH1_pairing_le_of_ae_spaceTime_le hImeas u hbound hψ hψnonneg

/-- The pairing order characterizes the spatial order on any compact set
contained in the spatial domain. -/
theorem ae_parH1_slice_le_on_compact_of_ae_spaceTime_le
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I) {M : ℝ}
    (hbound : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), u.toFun z ≤ M)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ t ∈ interior I,
      ∀ᵐ x ∂(volumeOn K), u.toFun (x, t) ≤ M := by
  intro t ht
  have hslice := u.sliceL2loc t (interior_subset ht) K hK hKU
  let : IsFiniteMeasure (volumeOn K) := ⟨by
    simpa [volumeOn, Measure.restrict_apply MeasurableSet.univ] using
      hK.measure_lt_top⟩
  have hf : Integrable (fun x => u.toFun (x, t)) (volumeOn K) :=
    hslice.integrable (by norm_num)
  have hg : Integrable (fun _ : Vec d => M) (volumeOn K) := integrable_const M
  have hset : ∀ E : Set (Vec d), MeasurableSet E → E ⊆ K →
      (∫ x in E, u.toFun (x, t) ∂volume) ≤
        ∫ x in E, M ∂volume := by
    intro E hE hEK
    let ψ : Vec d → ℝ := E.indicator (fun _ => (1 : ℝ))
    have hEU : E ⊆ U := hEK.trans hKU
    have hμE : volume E < ⊤ := (measure_mono hEK).trans_lt hK.measure_lt_top
    have hψL2 : IsL2c U ψ := by
      refine ⟨?_, ⟨K, hK, hKU, ?_⟩⟩
      · change MemLp ψ 2 (volumeOn U)
        exact memLp_indicator_const (μ := volumeOn U) (p := 2) hE 1
          (Or.inr (by
            apply ne_of_lt
            calc
              volumeOn U E ≤ volume E := by
                rw [volumeOn, Measure.restrict_apply hE]
                exact measure_mono (by
                  intro x hx
                  exact hx.1)
              _ < ⊤ := hμE))
      · intro x hxK
        dsimp [ψ]
        apply indicator_of_notMem
        intro hxE
        exact hxK (hEK hxE)
    have hψnonneg : ∀ x, 0 ≤ ψ x := by
      intro x
      by_cases hx : x ∈ E <;> simp [ψ, hx]
    have hpair := parH1_pairing_le_at_every_interior_time_of_ae_spaceTime_le
      hImeas u hbound hψL2 hψnonneg t ht
    have hleft : (∫ x in U, u.toFun (x, t) * ψ x) =
        ∫ x in E, u.toFun (x, t) ∂volume := by
      have hfun : (fun x => u.toFun (x, t) * ψ x) =
          E.indicator (fun x => u.toFun (x, t)) := by
        funext x
        by_cases hx : x ∈ E <;> simp [ψ, hx]
      rw [hfun]
      calc
        ∫ x in U, E.indicator (fun x => u.toFun (x, t)) x ∂volume =
            ∫ x, E.indicator (fun x => u.toFun (x, t)) x ∂volume := by
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          filter_upwards [] with x
          intro hxU
          simp [show x ∉ E from fun hxE => hxU (hEU hxE)]
        _ = ∫ x in E, u.toFun (x, t) ∂volume := integral_indicator hE
    have hmass : (∫ x in U, ψ x) = volume.real E := by
      calc
        ∫ x in U, ψ x ∂volume = ∫ x, ψ x ∂volume := by
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          filter_upwards [] with x
          intro hxU
          simp [ψ, show x ∉ E from fun hxE => hxU (hEU hxE)]
        _ = volume.real E := by
          change ∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂volume = _
          exact integral_indicator_one hE
    calc
      ∫ x in E, u.toFun (x, t) ∂volume =
          ∫ x in U, u.toFun (x, t) * ψ x := hleft.symm
      _ ≤ M * volume.real E := by rw [← hmass]; exact hpair
      _ = ∫ x in E, M ∂volume := by
        rw [setIntegral_const]
        rw [Measure.real_def]
        ring
  apply ae_le_of_forall_setIntegral_le hf hg
  intro E hE hμ
  let E' := E ∩ K
  have hE'meas : MeasurableSet E' := hE.inter hK.measurableSet
  have hE'bound := hset E' hE'meas inter_subset_right
  simpa [E', volumeOn, Measure.restrict_restrict, inter_comm, Measure.real, hE] using hE'bound

/-- The lower-order version of the compact slice transfer, obtained by
applying the upper-order result to the negated parabolic energy function. -/
theorem ae_parH1_slice_ge_on_compact_of_ae_spaceTime_ge
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I) {m : ℝ}
    (hbound : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), m ≤ u.toFun z)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ t ∈ interior I,
      ∀ᵐ x ∂(volumeOn K), m ≤ u.toFun (x, t) := by
  have hneg : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)),
      (negParH1Function u).toFun z ≤ -m := by
    filter_upwards [hbound] with z hz
    exact neg_le_neg hz
  have hslice := ae_parH1_slice_le_on_compact_of_ae_spaceTime_le
    hImeas (negParH1Function u) hneg hK hKU
  intro t ht
  filter_upwards [hslice t ht] with x hx
  change -u.toFun (x, t) ≤ -m at hx
  linarith

/-- Essential-supremum form of the upper time-slice transfer. -/
theorem parH1_slice_essSup_ofReal_le_of_ae_spaceTime_le
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I) {M : ℝ}
    (hbound : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), u.toFun z ≤ M)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ t ∈ interior I,
      essSup (fun x => ENNReal.ofReal (u.toFun (x, t))) (volumeOn K) ≤
        ENNReal.ofReal M := by
  have hslice := ae_parH1_slice_le_on_compact_of_ae_spaceTime_le
    hImeas u hbound hK hKU
  intro t ht
  have hENN : ∀ᵐ x ∂(volumeOn K),
      ENNReal.ofReal (u.toFun (x, t)) ≤ ENNReal.ofReal M :=
    (hslice t ht).mono fun x hx => ENNReal.ofReal_le_ofReal hx
  exact essSup_le_of_ae_le _ hENN

/-- Essential-infimum form of the lower time-slice transfer. -/
theorem parH1_slice_essInf_ofReal_ge_of_ae_spaceTime_ge
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I) {m : ℝ}
    (hbound : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), m ≤ u.toFun z)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ t ∈ interior I,
      ENNReal.ofReal m ≤
        essInf (fun x => ENNReal.ofReal (u.toFun (x, t))) (volumeOn K) := by
  have hslice := ae_parH1_slice_ge_on_compact_of_ae_spaceTime_ge
    hImeas u hbound hK hKU
  intro t ht
  have hENN : ∀ᵐ x ∂(volumeOn K),
      ENNReal.ofReal m ≤ ENNReal.ofReal (u.toFun (x, t)) :=
    (hslice t ht).mono fun x hx => ENNReal.ofReal_le_ofReal hx
  exact le_essInf_of_ae_le _ hENN

/-- **Two-time-slice order transfer.** Space-time upper and lower estimates on
compact spatial sets, together with a scalar comparison `M ≤ H m`, imply the
corresponding essential-supremum/essential-infimum comparison at any two
interior times.  This is the final continuity step used after the local
space-time estimates in the parabolic Harnack argument. -/
theorem parH1_two_time_slice_harnack_of_spaceTime_bounds
    {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}
    (hImeas : MeasurableSet I) (u : ParH1Function U I)
    {M m H : ℝ} (hH : 0 ≤ H) (hMm : M ≤ H * m)
    (hupper : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), u.toFun z ≤ M)
    (hlower : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), m ≤ u.toFun z)
    {K₀ K₁ : Set (Vec d)} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hK₀U : K₀ ⊆ U) (hK₁U : K₁ ⊆ U)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ interior I) (ht₁ : t₁ ∈ interior I) :
    essSup (fun x => ENNReal.ofReal (u.toFun (x, t₀))) (volumeOn K₀) ≤
      ENNReal.ofReal H *
        essInf (fun x => ENNReal.ofReal (u.toFun (x, t₁))) (volumeOn K₁) := by
  have hsup := parH1_slice_essSup_ofReal_le_of_ae_spaceTime_le
    hImeas u hupper hK₀ hK₀U t₀ ht₀
  have hinf := parH1_slice_essInf_ofReal_ge_of_ae_spaceTime_ge
    hImeas u hlower hK₁ hK₁U t₁ ht₁
  calc
    essSup (fun x => ENNReal.ofReal (u.toFun (x, t₀))) (volumeOn K₀) ≤
        ENNReal.ofReal M := hsup
    _ ≤ ENNReal.ofReal (H * m) := ENNReal.ofReal_le_ofReal hMm
    _ = ENNReal.ofReal H * ENNReal.ofReal m := ENNReal.ofReal_mul hH
    _ ≤ ENNReal.ofReal H *
        essInf (fun x => ENNReal.ofReal (u.toFun (x, t₁))) (volumeOn K₁) :=
      mul_le_mul_of_nonneg_left hinf (by positivity)

end PDE.Parabolic.Moser
