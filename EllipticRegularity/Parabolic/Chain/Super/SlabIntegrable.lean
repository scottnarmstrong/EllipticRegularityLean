/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.CompositionLimit
public import EllipticRegularity.Parabolic.Chain.SmoothSolution
public import EllipticRegularity.Parabolic.Energy.Bridge

/-! # Integrability of the renormalized integrand and of `F(u) φ`

For a `C¹` weight `φ` vanishing outside a compact lateral set `K ⊆ U`, the renormalized integrand
of an `H¹_par` function is integrable on every bounded measurable time slab `U × J`, `J ⊆ I`, and
so are the slab integrand `F(u) φ` and the time slices `x ↦ F(u(x,τ)) φ(x,τ)`.
-/

@[expose] public section

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Energy

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ} {a : ParCoeffField d}

/-- `φ` vanishing off `K × ℝ` has zero derivative there. -/
theorem fderiv_eq_zero_of_lateral {φ : Vec d × ℝ → ℝ} {K : Set (Vec d)} (hK : IsCompact K)
    (hφK : ∀ x ∉ K, ∀ τ, φ (x, τ) = 0) {z : Vec d × ℝ} (hz : z.1 ∉ K) :
    fderiv ℝ φ z = 0 := by
  have hopen : IsOpen (Kᶜ ×ˢ (univ : Set ℝ)) := hK.isClosed.isOpen_compl.prod isOpen_univ
  have hloc : φ =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds ⟨hz, mem_univ _⟩)
      (fun w hw => hφK w.1 hw.1 w.2)
  rw [hloc.fderiv_eq]
  simp

section

variable {F : ℝ → ℝ} {φ : Vec d × ℝ → ℝ} {K : Set (Vec d)} {p q : ℝ} {J : Set ℝ}

/-- Continuous functions are bounded almost everywhere on a compact lateral slab. -/
theorem exists_ae_bound_slab {f : Vec d × ℝ → ℝ} (hf : Continuous f) (hK : IsCompact K)
    (hJ : J ⊆ Icc p q) (hJm : MeasurableSet J) (hKm : MeasurableSet K) :
    ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict (K ×ˢ J)), |f z| ≤ M := by
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_Icc (a := p) (b := q))).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨M, (ae_restrict_iff' (hKm.prod hJm)).2 (Eventually.of_forall fun z hz => ?_)⟩
  simpa [Real.norm_eq_abs] using hM z ⟨hz.1, hJ hz.2⟩

theorem restrict_slab_le (hKU : K ⊆ U) (hJI : J ⊆ I) :
    volume.restrict (K ×ˢ J) ≤ volume.restrict (U ×ˢ I) :=
  Measure.restrict_mono (prod_mono hKU hJI) le_rfl

theorem isFiniteMeasure_slab (hK : IsCompact K) (hJ : J ⊆ Icc p q) :
    IsFiniteMeasure (volume.restrict (K ×ˢ J)) :=
  ⟨by
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    refine ENNReal.mul_lt_top hK.measure_lt_top ?_
    exact (measure_mono hJ).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)⟩

/-- The slab integrand `F(u) φ` is integrable. -/
theorem integrableOn_Fu_mul (hU : IsOpen U) (u : ParH1Function U I)
    (hFLip : ∃ C : NNReal, LipschitzWith C F) (hφ : Continuous φ) (hK : IsCompact K)
    (hKU : K ⊆ U) (hφK : ∀ x ∉ K, ∀ τ, φ (x, τ) = 0) (hpq : Icc p q ⊆ I)
    (hJ : J ⊆ Icc p q) (hJm : MeasurableSet J) :
    IntegrableOn (fun z => F (u.toFun z) * φ z) (U ×ˢ J) := by
  have := isFiniteMeasure_slab hK hJ
  have hJI : J ⊆ I := hJ.trans hpq
  have huL2 : MemLp u.toFun 2 (volume.restrict (K ×ˢ J)) :=
    u.memL2.mono_measure (restrict_slab_le hKU hJI)
  have hFuL2 := memLp_comp_lipschitz hFLip huL2
  obtain ⟨M, hM⟩ := exists_ae_bound_slab hφ hK hJ hJm hK.measurableSet
  have hK' : IntegrableOn (fun z => F (u.toFun z) * φ z) (K ×ˢ J) := by
    have := (hFuL2.integrable one_le_two).bdd_mul (f := φ) hφ.aestronglyMeasurable (c := M)
      (hM.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
    refine this.congr (Eventually.of_forall fun z => ?_)
    ring
  refine hK'.of_forall_sdiff_eq_zero (hU.measurableSet.prod hJm) ?_
  rintro ⟨x, τ⟩ ⟨⟨hxU, hτ⟩, hn⟩
  have hxK : x ∉ K := fun hx => hn ⟨hx, hτ⟩
  simp [hφK x hxK τ]

/-- The renormalized integrand is integrable on bounded time slabs. -/
theorem integrableOn_renormalizedIntegrand (hU : IsOpen U)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hF : ContDiff ℝ 2 F) (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (hφ : ContDiff ℝ 1 φ) (hK : IsCompact K)
    (hKU : K ⊆ U) (hφK : ∀ x ∉ K, ∀ τ, φ (x, τ) = 0) (hpq : Icc p q ⊆ I)
    (hJ : J ⊆ Icc p q) (hJm : MeasurableSet J) :
    IntegrableOn (renormalizedIntegrand a u F φ) (U ×ˢ J) := by
  have := isFiniteMeasure_slab hK hJ
  have hJI : J ⊆ I := hJ.trans hpq
  obtain ⟨C1, hC1⟩ := hF'bound
  obtain ⟨C2, hC2⟩ := hF''bound
  set ν := volume.restrict (K ×ˢ J) with hν
  have hle := restrict_slab_le hKU hJI
  have huL2 : MemLp u.toFun 2 ν := u.memL2.mono_measure hle
  have hFuL2 := memLp_comp_lipschitz hFLip huL2
  have hF1 := contDiff_deriv_of_two hF
  have hF'c : Continuous (deriv F) := hF1.continuous
  have hF''c : Continuous (deriv (deriv F)) := hF1.continuous_deriv (by norm_num)
  have hum : AEStronglyMeasurable u.toFun ν := huL2.aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun z => deriv F (u.toFun z)) ν :=
    hF'c.aestronglyMeasurable.comp_aemeasurable hum.aemeasurable
  have hF''meas : AEStronglyMeasurable (fun z => deriv (deriv F) (u.toFun z)) ν :=
    hF''c.aestronglyMeasurable.comp_aemeasurable hum.aemeasurable
  have hφc : Continuous φ := hφ.continuous
  have htc : Continuous (parTimeDeriv φ) := by
    unfold parTimeDeriv
    exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgc : ∀ i, Continuous fun z => parSpaceGrad φ z i := fun i => by
    unfold parSpaceGrad
    exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hone : MemLp (fun _ : Vec d × ℝ => (1 : ℝ)) 2 ν := memLp_const 1
  obtain ⟨Mt, hMt⟩ := exists_ae_bound_slab htc hK hJ hJm hK.measurableSet
  obtain ⟨Mφ, hMφ⟩ := exists_ae_bound_slab hφc hK hJ hJm hK.measurableSet
  have hflux : ∀ i, MemLp (fun z => flux a u z i) 2 ν := fun i =>
    (flux_memLp ha u i).mono_measure hle
  have hgrad : ∀ i, MemLp (fun z => u.grad z i) 2 ν := fun i =>
    (u.gradMemL2 i).mono_measure hle
  -- the three terms
  have T1 : Integrable (fun z => -(F (u.toFun z) * parTimeDeriv φ z)) ν := by
    have := (hFuL2.integrable one_le_two).bdd_mul (f := parTimeDeriv φ)
      htc.aestronglyMeasurable (c := Mt) (hMt.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
    refine (this.congr (Eventually.of_forall fun z => ?_)).neg
    ring
  have T2 : Integrable (fun z => deriv F (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ z)) ν := by
    have hsum : Integrable (fun z => ∑ i, (deriv F (u.toFun z) * parSpaceGrad φ z i) *
        flux a u z i * 1) ν := by
      refine integrable_finsetSum _ fun i _ => ?_
      obtain ⟨Mg, hMg⟩ := exists_ae_bound_slab (hgc i) hK hJ hJm hK.measurableSet
      refine PDE.Parabolic.Energy.integrable_weight_mul (M := C1 * |Mg|)
        (hF'meas.mul (hgc i).aestronglyMeasurable) ?_ (hflux i) hone
      filter_upwards [hMg] with z hz
      rw [abs_mul]
      exact mul_le_mul (hC1 _) (hz.trans (le_abs_self _)) (abs_nonneg _) (by positivity)
    refine hsum.congr (Eventually.of_forall fun z => ?_)
    simp only [vecDot, flux, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have T3 : Integrable (fun z => deriv (deriv F) (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z)) (u.grad z) * φ z) ν := by
    have hsum : Integrable (fun z => ∑ i, (deriv (deriv F) (u.toFun z) * φ z) *
        flux a u z i * u.grad z i) ν := by
      refine integrable_finsetSum _ fun i _ => ?_
      refine PDE.Parabolic.Energy.integrable_weight_mul (M := C2 * |Mφ|)
        (hF''meas.mul hφc.aestronglyMeasurable) ?_ (hflux i) (hgrad i)
      filter_upwards [hMφ] with z hz
      rw [abs_mul]
      exact mul_le_mul (hC2 _) (hz.trans (le_abs_self _)) (abs_nonneg _) (by positivity)
    refine hsum.congr (Eventually.of_forall fun z => ?_)
    simp only [vecDot, flux, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hK' : IntegrableOn (renormalizedIntegrand a u F φ) (K ×ˢ J) :=
    (T1.add T2).add T3
  refine hK'.of_forall_sdiff_eq_zero (hU.measurableSet.prod hJm) ?_
  rintro ⟨x, τ⟩ ⟨⟨hxU, hτ⟩, hn⟩
  have hxK : x ∉ K := fun hx => hn ⟨hx, hτ⟩
  have hfd : fderiv ℝ φ (x, τ) = 0 := fderiv_eq_zero_of_lateral hK hφK hxK
  have h1 : parTimeDeriv φ (x, τ) = 0 := by simp [parTimeDeriv, hfd]
  have h2 : parSpaceGrad φ (x, τ) = 0 := by
    ext i; simp [parSpaceGrad, hfd]
  unfold renormalizedIntegrand
  rw [h1, h2, hφK x hxK τ]
  simp [vecDot]

/-- The time slices `x ↦ F(u(x,τ)) φ(x,τ)` are integrable for `τ ∈ I`. -/
theorem integrableOn_slice_Fu_mul (hU : IsOpen U) (u : ParH1Function U I)
    (hFLip : ∃ C : NNReal, LipschitzWith C F) (hφ : Continuous φ) (hK : IsCompact K)
    (hKU : K ⊆ U) (hφK : ∀ x ∉ K, ∀ τ, φ (x, τ) = 0) {τ : ℝ} (hτ : τ ∈ I) :
    IntegrableOn (fun x => F (u.toFun (x, τ)) * φ (x, τ)) U := by
  have hL2 : MemLp (parSlice u.toFun τ) 2 (volume.restrict K) := u.sliceL2loc τ hτ K hK hKU
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hFL2 := memLp_comp_lipschitz hFLip hL2
  have hφs : Continuous fun x => φ (x, τ) := hφ.comp (continuous_id.prodMk continuous_const)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφs.continuousOn
  have hK' : IntegrableOn (fun x => F (u.toFun (x, τ)) * φ (x, τ)) K := by
    have := (hFL2.integrable one_le_two).bdd_mul (f := fun x => φ (x, τ))
      hφs.aestronglyMeasurable (c := M)
      ((ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx => hM x hx))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [parSlice]
    ring
  refine hK'.of_forall_sdiff_eq_zero hU.measurableSet fun x hx => ?_
  simp [hφK x (fun h => hx.2 h) τ]

end

end PDE.Parabolic.Chain.Super
