module

public import EllipticRegularity.Parabolic.Cauchy.Lions.JointField
public import EllipticRegularity.Parabolic.Energy.Slab
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Slice gradients of joint Lions limits

The joint closure identity is tested against products of a spatial test and a time cutoff. Fubini
and the fundamental lemma in time then give the weak spatial-gradient identity on almost every
time slice.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace PDE.Parabolic.Lions

def cauchySlabSet (d : ℕ) (s T : ℝ) : Set (Vec d × ℝ) :=
  (univ : Set (Vec d)) ×ˢ Icc s T

private theorem cauchy_locallyIntegrable_integral_mul {d : ℕ}
    {f : ℝ × Vec d → ℝ} (hf : LocallyIntegrable f (volume : Measure (ℝ × Vec d)))
    {b : Vec d → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b) :
    LocallyIntegrable (fun t => ∫ x, f (t, x) * b x) (volume : Measure ℝ) := by
  rw [locallyIntegrable_iff]
  intro K hK
  let B : Set (Vec d) := tsupport b
  have hKB : IsCompact (K ×ˢ B) := hK.prod hbc.isCompact
  have h1 : IntegrableOn (fun p : ℝ × Vec d => f p * b p.2) (K ×ˢ B)
      (volume : Measure (ℝ × Vec d)) :=
    (hf.integrableOn_isCompact hKB).mul_continuousOn (hb.comp continuous_snd).continuousOn hKB
  have h2 : IntegrableOn (fun p : ℝ × Vec d => f p * b p.2) (K ×ˢ univ)
      (volume : Measure (ℝ × Vec d)) := by
    refine h1.of_forall_sdiff_eq_zero (hK.measurableSet.prod MeasurableSet.univ) ?_
    rintro ⟨t, x⟩ ⟨hp, hx⟩
    rcases hp with ⟨htK, _⟩
    have hxB : x ∉ B := fun hxB => hx ⟨htK, hxB⟩
    simp [image_eq_zero_of_notMem_tsupport hxB]
  have h3 : Integrable (fun p : ℝ × Vec d => f p * b p.2)
      ((volume.restrict K).prod (volume : Measure (Vec d))) := by
    have hprod := Measure.prod_restrict (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Vec d))) K univ
    rw [Measure.restrict_univ] at hprod
    rw [hprod, ← Measure.volume_eq_prod]
    exact h2
  exact h3.integral_prod_left

private theorem cauchy_swap_volume (d : ℕ) :
    MeasurePreserving (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume : Measure (ℝ × Vec d)) (volume : Measure (Vec d × ℝ)) := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact Measure.measurePreserving_swap

/-- Zero extension of the value component of a joint Lions limit. -/
noncomputable def cauchyExtendedValue {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (z : Vec d × ℝ) : ℝ :=
  (cauchySlabSet d s T).indicator (cauchyJointValue u) z

/-- Zero extension of a coordinate of the gradient component of a joint Lions limit. -/
noncomputable def cauchyExtendedGradient {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (i : Fin d) (z : Vec d × ℝ) : ℝ :=
  (cauchySlabSet d s T).indicator (fun z => cauchyJointGradient u z i) z

theorem cauchyExtendedValue_memLp {d : ℕ} {s T : ℝ} (u : CauchyX d s T) :
    MemLp (cauchyExtendedValue u) 2 (volume : Measure (Vec d × ℝ)) := by
  unfold cauchyExtendedValue cauchySlabSet
  rw [memLp_indicator_iff_restrict (MeasurableSet.univ.prod measurableSet_Icc)]
  exact cauchyJointValue_memLp u

theorem cauchyExtendedGradient_memLp {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (i : Fin d) :
    MemLp (cauchyExtendedGradient u i) 2 (volume : Measure (Vec d × ℝ)) := by
  unfold cauchyExtendedGradient cauchySlabSet
  rw [memLp_indicator_iff_restrict (MeasurableSet.univ.prod measurableSet_Icc)]
  exact cauchyJointGradient_memLp u i

private theorem cauchyExtended_ae_slice_memLp {d : ℕ} {s T : ℝ} (u : CauchyX d s T) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyJointValue u (x, t)) 2 (volume : Measure (Vec d)) := by
  have hLp : MemLp (cauchyJointValue u) 2
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)) := by
    exact cauchyJointValue_memLp u
  exact PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := Icc s T) (g := cauchyJointValue u) MeasurableSet.univ hLp |>.mono fun t ht => by
      simpa using ht

private theorem cauchyExtendedGradient_ae_slice_memLp {d : ℕ} {s T : ℝ}
    (u : CauchyX d s T) (i : Fin d) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyJointGradient u (x, t) i) 2
        (volume : Measure (Vec d)) := by
  have hLp : MemLp (fun z => cauchyJointGradient u z i) 2
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)) := by
    exact cauchyJointGradient_memLp u i
  exact PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := Icc s T) (g := fun z => cauchyJointGradient u z i) MeasurableSet.univ hLp |>.mono
      fun t ht => by simpa using ht

private theorem cauchyExtendedValue_ae_slice_memLp_global {d : ℕ} {s T : ℝ}
    (u : CauchyX d s T) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      MemLp (fun x : Vec d => cauchyExtendedValue u (x, t)) 2 (volume : Measure (Vec d)) := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := (univ : Set ℝ)) (g := cauchyExtendedValue u) MeasurableSet.univ
    (by simpa using cauchyExtendedValue_memLp u)
  have h' : ∀ᵐ t ∂(volume : Measure ℝ),
      MemLp (univ.indicator fun y => cauchyExtendedValue u (y, t)) 2
        (volume : Measure (Vec d)) := by
    simpa only [Measure.restrict_univ] using h
  filter_upwards [h'] with t ht
  simpa using ht

private theorem cauchyExtendedGradient_ae_slice_memLp_global {d : ℕ} {s T : ℝ}
    (u : CauchyX d s T) (i : Fin d) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      MemLp (fun x : Vec d => cauchyExtendedGradient u i (x, t)) 2
        (volume : Measure (Vec d)) := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := (univ : Set ℝ)) (g := cauchyExtendedGradient u i) MeasurableSet.univ
    (by simpa using cauchyExtendedGradient_memLp u i)
  have h' : ∀ᵐ t ∂(volume : Measure ℝ),
      MemLp (univ.indicator fun y => cauchyExtendedGradient u i (y, t)) 2
        (volume : Measure (Vec d)) := by
    simpa only [Measure.restrict_univ] using h
  filter_upwards [h'] with t ht
  simpa using ht

private theorem cauchy_tensor_spacetime_identity {d : ℕ} {s T : ℝ}
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hu : WithLp.toLp 2 (u, u₀) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ)
    (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆ Ioo s T) (i : Fin d) :
    ∫ t, θ t * (∫ x, cauchyExtendedValue u (x, t) * spaceGradC1 ψ x i +
      cauchyExtendedGradient u i (x, t) * ψ x) ∂(volume : Measure ℝ) = 0 := by
  let Φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)) := {
    toFun := fun z => θ z.2 * ψ z.1
    contDiff := PDE.Parabolic.WeakSlice.contDiff_prod hθ (hψ.of_le (by norm_num))
    hasCompactSupport := PDE.Parabolic.WeakSlice.hasCompactSupport_prod hθc hψc
    tsupport_subset := by
      have hI : Ioo s T ⊆ interior (Icc s T) := by
        refine interior_maximal ?_ isOpen_Ioo
        intro t ht
        exact ⟨ht.1.le, ht.2.le⟩
      exact PDE.Parabolic.WeakSlice.tsupport_prod_subset.trans
        (prod_mono (subset_univ _) (hθs.trans hI)) }
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have htestGradC : Continuous (fun z => parSpaceGrad Φ.toFun z i) :=
    (continuous_apply i).comp (continuous_parSpaceGrad Φ.contDiff)
  have htestGradK : HasCompactSupport (fun z => parSpaceGrad Φ.toFun z i) := by
    apply HasCompactSupport.of_support_subset_isCompact Φ.hasCompactSupport.isCompact
    intro z hz
    by_contra hzΦ
    have hD : fderiv ℝ Φ.toFun z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hzΦ (tsupport_fderiv_subset ℝ h))
    exact hz (by simp [parSpaceGrad, hD])
  have htestGrad : MemLp (fun z => parSpaceGrad Φ.toFun z i) 2
      (volume : Measure (Vec d × ℝ)) := htestGradC.memLp_of_hasCompactSupport htestGradK
  have htest : MemLp Φ.toFun 2 (volume : Measure (Vec d × ℝ)) :=
    Φ.contDiff.continuous.memLp_of_hasCompactSupport Φ.hasCompactSupport
  have hval := cauchyExtendedValue_memLp u
  have hgrad := cauchyExtendedGradient_memLp u i
  have hL : Integrable (fun z => cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i)
      (volume : Measure (Vec d × ℝ)) := hval.integrable_mul htestGrad
  have hR : Integrable (fun z => cauchyExtendedGradient u i z * Φ.toFun z)
      (volume : Measure (Vec d × ℝ)) := hgrad.integrable_mul htest
  have hwhole : Integrable
      (fun z => cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i +
        cauchyExtendedGradient u i z * Φ.toFun z)
      (volume : Measure (Vec d × ℝ)) := hL.add hR
  have hweak := cauchyClosure_spacetimeWeakGradient hu Φ i
  have hsetL : ∫ z, cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i
      ∂(volume : Measure (Vec d × ℝ)) =
      ∫ z, cauchyJointValue u z * parSpaceGrad Φ.toFun z i ∂slabMeasure d s T := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := cauchySlabSet d s T)]
    · rw [slabMeasure]
      apply setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc)
      intro z hz
      have hz' : z ∈ (univ : Set (Vec d)) ×ˢ Icc s T := by
        simpa [cauchySlabSet] using hz
      simp [cauchyExtendedValue, cauchySlabSet, hz']
    · intro z hz
      have hz' : z ∉ (univ : Set (Vec d)) ×ˢ Icc s T := by
        simpa [cauchySlabSet] using hz
      simp [cauchyExtendedValue, cauchySlabSet, hz']
  have hsetR : ∫ z, cauchyExtendedGradient u i z * Φ.toFun z
      ∂(volume : Measure (Vec d × ℝ)) =
      ∫ z, cauchyJointGradient u z i * Φ.toFun z ∂slabMeasure d s T := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := cauchySlabSet d s T)]
    · rw [slabMeasure]
      apply setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc)
      intro z hz
      have hz' : z ∈ (univ : Set (Vec d)) ×ˢ Icc s T := by
        simpa [cauchySlabSet] using hz
      simp [cauchyExtendedGradient, cauchySlabSet, hz']
    · intro z hz
      have hz' : z ∉ (univ : Set (Vec d)) ×ˢ Icc s T := by
        simpa [cauchySlabSet] using hz
      simp [cauchyExtendedGradient, cauchySlabSet, hz']
  have hsum : ∫ z, cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i +
      cauchyExtendedGradient u i z * Φ.toFun z ∂(volume : Measure (Vec d × ℝ)) = 0 := by
    rw [integral_add hL hR, hsetL, hsetR]
    exact add_eq_zero_iff_eq_neg.mpr hweak
  have hgradFormula (z : Vec d × ℝ) :
      parSpaceGrad Φ.toFun z i = θ z.2 * spaceGradC1 ψ z.1 i := by
    change parSpaceGrad (fun w : Vec d × ℝ => θ w.2 * ψ w.1) z i = _
    exact congrFun (PDE.Parabolic.WeakSlice.parSpaceGrad_prod hθ hψ1 z) i
  have hq : Integrable
      (fun z => θ z.2 * (cauchyExtendedValue u z * spaceGradC1 ψ z.1 i +
        cauchyExtendedGradient u i z * ψ z.1)) (volume : Measure (Vec d × ℝ)) := by
    refine hwhole.congr ?_
    exact Filter.Eventually.of_forall fun z => by
      change cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i +
        cauchyExtendedGradient u i z * Φ.toFun z = _
      rw [hgradFormula z]
      ring
  have hfactor :
      (∫ z, cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i +
        cauchyExtendedGradient u i z * Φ.toFun z ∂(volume : Measure (Vec d × ℝ))) =
      ∫ z, θ z.2 * (cauchyExtendedValue u z * spaceGradC1 ψ z.1 i +
        cauchyExtendedGradient u i z * ψ z.1) ∂(volume : Measure (Vec d × ℝ)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change cauchyExtendedValue u z * parSpaceGrad Φ.toFun z i +
        cauchyExtendedGradient u i z * Φ.toFun z = _
      rw [hgradFormula z]
      ring
  rw [hfactor, Measure.volume_eq_prod, integral_prod_symm _ hq] at hsum
  have hfactorTime :
      (∫ (t : ℝ), θ t * (∫ (x : Vec d), cauchyExtendedValue u (x, t) * spaceGradC1 ψ x i +
        cauchyExtendedGradient u i (x, t) * ψ x ∂(volume : Measure (Vec d)))
        ∂(volume : Measure ℝ)) =
      ∫ (t : ℝ), ∫ (x : Vec d), θ t * (cauchyExtendedValue u (x, t) * spaceGradC1 ψ x i +
        cauchyExtendedGradient u i (x, t) * ψ x) ∂(volume : Measure (Vec d))
      ∂(volume : Measure ℝ) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun (t : ℝ) => by
      change θ t * (∫ (x : Vec d), cauchyExtendedValue u (x, t) * spaceGradC1 ψ x i +
        cauchyExtendedGradient u i (x, t) * ψ x ∂(volume : Measure (Vec d))) = _
      rw [← integral_const_mul]
  exact hfactorTime.trans hsum

/-- For a fixed smooth spatial test, the spatial weak-gradient identity holds for almost every
time. -/
theorem cauchyClosure_fixedSliceTest {d : ℕ} {s T : ℝ}
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hu : WithLp.toLp 2 (u, u₀) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i : Fin d) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      ∫ x, cauchyJointValue u (x, t) * spaceGradC1 ψ x i =
        -∫ x, cauchyJointGradient u (x, t) i * ψ x := by
  let Dψ : Vec d → ℝ := fun x => spaceGradC1 ψ x i
  have hDψC : Continuous Dψ := by
    dsimp [Dψ, spaceGradC1]
    exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDψK : HasCompactSupport Dψ := by
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro x hx
    by_contra hxψ
    have hD : fderiv ℝ ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxψ (tsupport_fderiv_subset ℝ h))
    exact hx (by simp [Dψ, spaceGradC1, hD])
  have hswap : MeasurePreserving (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume : Measure (ℝ × Vec d)) (volume : Measure (Vec d × ℝ)) := cauchy_swap_volume d
  let U : ℝ × Vec d → ℝ := fun p => cauchyExtendedValue u (p.2, p.1)
  let G : ℝ × Vec d → ℝ := fun p => cauchyExtendedGradient u i (p.2, p.1)
  have hUm : MemLp U 2 (volume : Measure (ℝ × Vec d)) := by
    exact (cauchyExtendedValue_memLp u).comp_measurePreserving hswap
  have hGm : MemLp G 2 (volume : Measure (ℝ × Vec d)) := by
    exact (cauchyExtendedGradient_memLp u i).comp_measurePreserving hswap
  have hULoc : LocallyIntegrable U (volume : Measure (ℝ × Vec d)) := hUm.locallyIntegrable (by norm_num)
  have hGLoc : LocallyIntegrable G (volume : Measure (ℝ × Vec d)) := hGm.locallyIntegrable (by norm_num)
  have hA1 := cauchy_locallyIntegrable_integral_mul hULoc hDψC hDψK
  have hψC : Continuous ψ := hψ.continuous
  have hψLI : HasCompactSupport ψ := hψc
  have hA2 := cauchy_locallyIntegrable_integral_mul hGLoc hψC hψLI
  let A : ℝ → ℝ := fun t =>
    (∫ x, cauchyExtendedValue u (x, t) * Dψ x) +
      ∫ x, cauchyExtendedGradient u i (x, t) * ψ x
  have hALoc : LocallyIntegrable A (volume : Measure ℝ) := by
    exact hA1.add hA2
  have htest : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo s T → ∫ t, θ t • A t = 0 := by
    intro θ hθ hθc hθs
    have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
    have htensor := cauchy_tensor_spacetime_identity hu ψ hψ hψc θ hθ1 hθc hθs i
    have hDψL : MemLp Dψ 2 (volume : Measure (Vec d)) :=
      hDψC.memLp_of_hasCompactSupport hDψK
    have hψL : MemLp ψ 2 (volume : Measure (Vec d)) :=
      hψC.memLp_of_hasCompactSupport hψc
    have hsplit : ∫ t, θ t * (∫ x, (cauchyExtendedValue u (x, t) * Dψ x +
        cauchyExtendedGradient u i (x, t) * ψ x)) =
        ∫ t, θ t * ((∫ x, cauchyExtendedValue u (x, t) * Dψ x) +
          (∫ x, cauchyExtendedGradient u i (x, t) * ψ x)) := by
      apply integral_congr_ae
      filter_upwards [cauchyExtendedValue_ae_slice_memLp_global u,
        cauchyExtendedGradient_ae_slice_memLp_global u i] with t hUL hGL
      have h1 : Integrable (fun x => cauchyExtendedValue u (x, t) * Dψ x)
          (volume : Measure (Vec d)) := hUL.integrable_mul hDψL
      have h2 : Integrable (fun x => cauchyExtendedGradient u i (x, t) * ψ x)
          (volume : Measure (Vec d)) := hGL.integrable_mul hψL
      change θ t * (∫ x, cauchyExtendedValue u (x, t) * Dψ x +
        cauchyExtendedGradient u i (x, t) * ψ x) =
        θ t * ((∫ x, cauchyExtendedValue u (x, t) * Dψ x) +
          (∫ x, cauchyExtendedGradient u i (x, t) * ψ x))
      rw [integral_add h1 h2]
    have htensor' : ∫ t, θ t * (∫ x, (cauchyExtendedValue u (x, t) * Dψ x +
        cauchyExtendedGradient u i (x, t) * ψ x)) = 0 := by
      simpa [Dψ] using htensor
    rw [hsplit] at htensor'
    simpa [A, smul_eq_mul] using htensor'
  have hAae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hALoc.locallyIntegrableOn (Ioo s T)) htest
  have hends : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ s ∧ t ≠ T := by
    have hneqs : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ s := by
      rw [ae_iff]
      simp
    have hneqT : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ T := by
      rw [ae_iff]
      simp
    filter_upwards [hneqs, hneqT] with t hts htT
    exact ⟨hts, htT⟩
  have hAonIcc : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Icc s T → A t = 0 := by
    filter_upwards [hAae, hends] with t ht hend htI
    have ht' : t ∈ Ioo s T := by
      exact ⟨lt_of_le_of_ne htI.1 (Ne.symm hend.1), lt_of_le_of_ne htI.2 hend.2⟩
    exact ht ht'
  have hArestrict := (ae_restrict_iff' measurableSet_Icc).2 hAonIcc
  filter_upwards [hArestrict, cauchyExtended_ae_slice_memLp u,
    cauchyExtendedGradient_ae_slice_memLp u i, ae_restrict_mem measurableSet_Icc]
    with t hAt huL hgL htI
  have hDψL : MemLp Dψ 2 (volume : Measure (Vec d)) :=
    hDψC.memLp_of_hasCompactSupport hDψK
  have hψL : MemLp ψ 2 (volume : Measure (Vec d)) :=
    hψC.memLp_of_hasCompactSupport hψc
  have h1 : Integrable (fun x => cauchyJointValue u (x, t) * Dψ x)
      (volume : Measure (Vec d)) := huL.integrable_mul hDψL
  have h2 : Integrable (fun x => cauchyJointGradient u (x, t) i * ψ x)
      (volume : Measure (Vec d)) := hgL.integrable_mul hψL
  have hAeq : A t =
      (∫ x, cauchyJointValue u (x, t) * Dψ x) +
        ∫ x, cauchyJointGradient u (x, t) i * ψ x := by
    dsimp [A]
    have hUEq (x : Vec d) : cauchyExtendedValue u (x, t) = cauchyJointValue u (x, t) := by
      simp [cauchyExtendedValue, cauchySlabSet, htI]
    have hGEq (x : Vec d) : cauchyExtendedGradient u i (x, t) =
        cauchyJointGradient u (x, t) i := by
      simp [cauchyExtendedGradient, cauchySlabSet, htI]
    have hExt1 : Integrable (fun x => cauchyExtendedValue u (x, t) * Dψ x)
        (volume : Measure (Vec d)) := h1.congr (Eventually.of_forall fun x => by
          change cauchyJointValue u (x, t) * Dψ x =
            cauchyExtendedValue u (x, t) * Dψ x
          rw [hUEq x])
    have hExt2 : Integrable (fun x => cauchyExtendedGradient u i (x, t) * ψ x)
        (volume : Measure (Vec d)) := h2.congr (Eventually.of_forall fun x => by
          change cauchyJointGradient u (x, t) i * ψ x =
            cauchyExtendedGradient u i (x, t) * ψ x
          rw [hGEq x])
    calc
      (∫ x, cauchyExtendedValue u (x, t) * Dψ x) +
          ∫ x, cauchyExtendedGradient u i (x, t) * ψ x =
        ∫ x, cauchyExtendedValue u (x, t) * Dψ x +
          cauchyExtendedGradient u i (x, t) * ψ x := (integral_add hExt1 hExt2).symm
      _ = ∫ x, cauchyJointValue u (x, t) * Dψ x +
          cauchyJointGradient u (x, t) i * ψ x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change cauchyExtendedValue u (x, t) * Dψ x +
            cauchyExtendedGradient u i (x, t) * ψ x =
            cauchyJointValue u (x, t) * Dψ x +
              cauchyJointGradient u (x, t) i * ψ x
          rw [hUEq x, hGEq x]
      _ = (∫ x, cauchyJointValue u (x, t) * Dψ x) +
          ∫ x, cauchyJointGradient u (x, t) i * ψ x := integral_add h1 h2
  rw [hAeq] at hAt
  exact add_eq_zero_iff_eq_neg.mp hAt

end PDE.Parabolic.Lions
