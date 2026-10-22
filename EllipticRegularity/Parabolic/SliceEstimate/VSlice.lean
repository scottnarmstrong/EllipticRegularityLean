module

public import EllipticRegularity.Parabolic.WeakSlice.Result

/-!
# Time-derivative identity at every time: `∫ u(t) ζ - ∫ u(s) ζ = ∫_s^t ∫ v ζ`

For `v = ∂ₜu` given through product test functions (hypothesis `hv` of the slice lemma), the
slice pairing `τ ↦ ∫_U u(x,τ) ζ(x) dx` (continuous by weak continuity) has increments
`∫_s^t ∫_U v ζ` (the analogue of `weak_slice`, via du Bois-Reymond).
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology PDE PDE.Parabolic PDE.Parabolic.WeakSlice

variable {d : ℕ}

/-- A function in `L²(U × I)` times a compactly supported continuous function of `x` is integrable
on `U × J` for `J ⊆ I` of finite measure. -/
theorem integrableOn_mul_fst {U : Set (Vec d)} (hU : IsOpen U) {I : Set ℝ} {f : Vec d × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (U ×ˢ I))) {ζ : Vec d → ℝ} (hζ : Continuous ζ)
    (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) {J : Set ℝ} (hJI : J ⊆ I)
    (hJm : MeasurableSet J) (hJ : volume J < ⊤) :
    IntegrableOn (fun z : Vec d × ℝ => f z * ζ z.1) (U ×ˢ J) := by
  set K := tsupport ζ with hK
  have hKc : IsCompact K := hζc
  suffices hKJ : IntegrableOn (fun z : Vec d × ℝ => f z * ζ z.1) (K ×ˢ J) from by
    refine hKJ.of_forall_sdiff_eq_zero (hU.measurableSet.prod hJm) ?_
    rintro ⟨x, τ⟩ ⟨hz, hn⟩
    have hx : x ∉ K := fun hx => hn ⟨hx, hz.2⟩
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hKJU : K ×ˢ J ⊆ U ×ˢ I := prod_mono hζU hJI
  set ν := volume.restrict (K ×ˢ J) with hν
  have hνle : ν ≤ volume.restrict (U ×ˢ I) := Measure.restrict_mono hKJU le_rfl
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hKc.measure_lt_top hJ
  obtain ⟨C, hC⟩ := hζ.bounded_above_of_compact_support hζc
  have h1 : Integrable f ν := (hf.mono_measure hνle).integrable one_le_two
  exact h1.mul_bdd ((hζ.comp continuous_fst).aestronglyMeasurable) (c := C)
    (Eventually.of_forall fun z => hC z.1)

/-- The slice identity for the time derivative `v`. -/
theorem time_derivative_slice {U : Set (Vec d)} (hU : IsOpen U) {I : Set ℝ} (hI : I.OrdConnected)
    (u v : ParH1Function U I)
    (hv : ∀ ψ : ParTestFunction U (interior I),
      ∫ z in U ×ˢ I, v.toFun z * ψ.toFun z = -∫ z in U ×ˢ I, u.toFun z * parTimeDeriv ψ.toFun z)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s < t) :
    (∫ x in U, u.toFun (x, t) * ζ x) - (∫ x in U, u.toFun (x, s) * ζ x) =
      ∫ τ in Ioc s t, ∫ x in U, v.toFun (x, τ) * ζ x := by
  have hSub : Icc s t ⊆ I := hI.out hs ht
  have hIoo : Ioo s t ⊆ I := fun τ hτ => hSub ⟨hτ.1.le, hτ.2.le⟩
  have hIoo' : Ioo s t ⊆ interior I := interior_maximal hIoo isOpen_Ioo
  have hfinIcc : volume (Icc s t) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  -- integrability of `v ζ` on `U × [s,t]`
  have hvζ : IntegrableOn (fun z : Vec d × ℝ => v.toFun z * ζ z.1) (U ×ˢ Icc s t) :=
    integrableOn_mul_fst hU v.memL2 hζ.continuous hζc hζU hSub measurableSet_Icc hfinIcc
  obtain ⟨hgIcc, _⟩ := integral_prod_slices hvζ
  have hgIoo : IntegrableOn (fun τ => -∫ x in U, v.toFun (x, τ) * ζ x) (Ioo s t) :=
    hgIcc.neg.mono_set Ioo_subset_Icc_self
  -- the time-test identity
  have htest : ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ → tsupport θ ⊆ Ioo s t →
      ∫ τ in Ioo s t, slicePairing u ζ τ * deriv θ τ =
        ∫ τ in Ioo s t, (-∫ x in U, v.toFun (x, τ) * ζ x) * θ τ := by
    intro θ hθ hθc hθs
    let φ : ParTestFunction U (interior I) :=
      { toFun := fun w : Vec d × ℝ => θ w.2 * ζ w.1
        contDiff := contDiff_prod hθ hζ
        hasCompactSupport := hasCompactSupport_prod hθc hζc
        tsupport_subset := tsupport_prod_subset.trans (prod_mono hζU (hθs.trans hIoo')) }
    have hvφ := hv φ
    have hψL2 : MemLp (fun w : Vec d × ℝ => θ w.2 * ζ w.1) 2 (volume.restrict (U ×ˢ I)) :=
      (contDiff_prod hθ hζ).continuous.memLp_of_hasCompactSupport (hasCompactSupport_prod hθc hζc)
    have hψ'L2 : MemLp (fun w : Vec d × ℝ => deriv θ w.2 * ζ w.1) 2 (volume.restrict (U ×ˢ I)) := by
      have hc : Continuous fun w : Vec d × ℝ => deriv θ w.2 * ζ w.1 :=
        ((hθ.continuous_deriv le_rfl).comp continuous_snd).mul (hζ.continuous.comp continuous_fst)
      refine hc.memLp_of_hasCompactSupport ?_
      have hdc : HasCompactSupport (deriv θ) := hθc.deriv
      exact hasCompactSupport_prod hdc hζc
    have hA : IntegrableOn (fun z : Vec d × ℝ => v.toFun z * (θ z.2 * ζ z.1)) (U ×ˢ I) :=
      v.memL2.integrable_mul hψL2
    have hB : IntegrableOn (fun z : Vec d × ℝ => u.toFun z * (deriv θ z.2 * ζ z.1)) (U ×ˢ I) :=
      u.memL2.integrable_mul hψ'L2
    have hφ' : ∀ z, parTimeDeriv φ.toFun z = deriv θ z.2 * ζ z.1 := fun z =>
      parTimeDeriv_prod hθ hζ z
    simp only [hφ'] at hvφ
    change ∫ z in U ×ˢ I, v.toFun z * (θ z.2 * ζ z.1) =
      -∫ z in U ×ˢ I, u.toFun z * (deriv θ z.2 * ζ z.1) at hvφ
    obtain ⟨_, hfa⟩ := integral_prod_slices hA
    obtain ⟨_, hfb⟩ := integral_prod_slices hB
    rw [hfa, hfb] at hvφ
    have e1 : ∀ τ, ∫ x in U, v.toFun (x, τ) * (θ τ * ζ x) =
        (∫ x in U, v.toFun (x, τ) * ζ x) * θ τ := by
      intro τ
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
    have e2 : ∀ τ, ∫ x in U, u.toFun (x, τ) * (deriv θ τ * ζ x) =
        slicePairing u ζ τ * deriv θ τ := by
      intro τ
      unfold slicePairing
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
    simp only [e1, e2] at hvφ
    have r1 : ∀ f : ℝ → ℝ, (∀ τ, τ ∉ Ioo s t → f τ = 0) →
        ∫ τ in I, f τ = ∫ τ in Ioo s t, f τ := fun f hf =>
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hI.measurableSet hIoo
        fun τ hτ => hf τ hτ.2
    have hz : ∀ τ, τ ∉ Ioo s t → deriv θ τ = 0 := fun τ hτ =>
      image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs (tsupport_deriv_subset h')))
    have hz' : ∀ τ, τ ∉ Ioo s t → θ τ = 0 := fun τ hτ =>
      image_eq_zero_of_notMem_tsupport (fun h' => hτ (hθs h'))
    rw [r1 _ (fun τ hτ => by rw [hz' τ hτ, mul_zero]),
      r1 _ (fun τ hτ => by rw [hz τ hτ, mul_zero])] at hvφ
    have hneg : ∫ τ in Ioo s t, (-∫ x in U, v.toFun (x, τ) * ζ x) * θ τ =
        -∫ τ in Ioo s t, (∫ x in U, v.toFun (x, τ) * ζ x) * θ τ := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    rw [hneg]
    simp only [slicePairing] at hvφ ⊢
    linarith [hvφ]
  -- du Bois-Reymond
  have hmc := slicePairing_continuousOn u hζ hζc hζU
  let m' : ℝ → ℝ := fun τ => slicePairing u ζ (projIcc s t hst.le τ)
  have hm' : Continuous m' :=
    (hmc.mono hSub).comp_continuous continuous_projIcc.subtype_val
      (fun τ => (projIcc s t hst.le τ).2)
  have hdbr := dubois_reymond hst m' (fun τ => -∫ x in U, v.toFun (x, τ) * ζ x) hm' hgIoo
    (fun θ h1 h2 h3 => by
      have := htest θ h1 h2 h3
      rw [← this]
      refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
      simp only [m', projIcc_of_mem _ (Ioo_subset_Icc_self hτ)])
  simp only [m', projIcc_left, projIcc_right] at hdbr
  unfold slicePairing at hdbr
  rw [integral_neg] at hdbr
  have hvζIoc : IntegrableOn (fun z : Vec d × ℝ => v.toFun z * ζ z.1) (U ×ˢ Ioc s t) :=
    hvζ.mono_set (prod_mono subset_rfl Ioc_subset_Icc_self)
  rw [integral_Ioc_eq_integral_Ioo]
  linarith [hdbr]

end PDE.Parabolic.Slice
