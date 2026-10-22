/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.Calculus
public import EllipticRegularity.Parabolic.Chain.TimeChain
public import EllipticRegularity.Parabolic.Energy.Result

/-! # Nonlinear identities for the spatial mollifications used by Energy -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Chain

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

variable (D : Energy.Data d)

/-- At each point of the compact spatial support, the time chain rule and
vanishing endpoint values give the temporal identity for a spatial
mollification. -/
theorem time_integral_mollified_zero {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hφs : ∀ x, D.φ (x, D.s) = 0) (hφt : ∀ x, D.φ (x, D.t) = 0)
    {x : Vec d} (hx : x ∈ D.K) :
    ∫ τ in Ioc D.s D.t,
        (F (D.v a (x, τ)) * parTimeDeriv D.φ (x, τ) +
          deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ) = 0 := by
  have h := time_chain_identity D.hst.le (v := fun τ => D.v a (x, τ))
    (D := fun τ => D.Dh a x τ) (ψ := fun τ => D.φ (x, τ))
    (D.Dh_intervalIntegrable ha x) (fun τ hτ => D.v_rep ha haδ hx hτ)
    (D.contDiff_timeSlice x)
    (hF.of_le (by norm_num)) hFLip
  simp_rw [D.deriv_timeSlice x] at h
  rw [hφt x, hφs x] at h
  simp only [mul_zero, sub_self] at h
  rw [← intervalIntegral.integral_of_le D.hst.le]
  exact h.symm

/-- The time-slice chain rule integrated over the local cylinder. -/
theorem temporal_integral_identity {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hφs : ∀ x, D.φ (x, D.s) = 0) (hφt : ∀ x, D.φ (x, D.t) = 0) :
    Integrable (fun z => F (D.v a z) * parTimeDeriv D.φ z) D.μP ∧
      Integrable (fun z => deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2) D.μP ∧
      (∫ z, F (D.v a z) * parTimeDeriv D.φ z ∂D.μP) +
        ∫ z, deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2 ∂D.μP = 0 := by
  obtain ⟨M, hM⟩ := D.ae_v_bound ha haδ
  obtain ⟨Mφ, hMφ⟩ := D.ae_bound_on_slab D.parTimeDeriv_continuous
  have hIccCompact : IsCompact (Icc (-max M 0) (max M 0)) := isCompact_Icc
  obtain ⟨MF0, hMF0⟩ := hIccCompact.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨Mderiv, hMderiv⟩ := hF'bound
  obtain ⟨Cflux, hCflux, hDh⟩ := D.exists_Dh_le ha
  have hFval : ∀ᵐ z ∂D.μP, |F (D.v a z)| ≤ max MF0 0 := by
    filter_upwards [hM] with z hz
    have hv : D.v a z ∈ Icc (-max M 0) (max M 0) := by
      have habs := abs_le.mp hz
      rcases habs with ⟨hlo, hhi⟩
      constructor <;> linarith [le_max_left M 0]
    have hb := hMF0 (D.v a z) hv
    simpa only [Real.norm_eq_abs] using hb.trans (le_max_left _ _)
  have hFprimeMeas : AEStronglyMeasurable (fun z => deriv F (D.v a z)) D.μP := by
    have hcomp : AEStronglyMeasurable (deriv F) (Measure.map (D.v a) D.μP) :=
      (contDiff_deriv_of_two hF).continuous.measurable.aestronglyMeasurable
    exact hcomp.comp_aemeasurable (D.v_aestronglyMeasurable a).aemeasurable
  have hFmeas : AEStronglyMeasurable (fun z => F (D.v a z)) D.μP := by
    have hcomp : AEStronglyMeasurable F (Measure.map (D.v a) D.μP) :=
      hF.continuous.measurable.aestronglyMeasurable
    exact hcomp.comp_aemeasurable (D.v_aestronglyMeasurable a).aemeasurable
  have htimeMeas : AEStronglyMeasurable (parTimeDeriv D.φ) D.μP :=
    D.parTimeDeriv_continuous.aestronglyMeasurable
  obtain ⟨Mφval, hMφval⟩ := D.ae_bound_on_slab D.phi_continuous
  have hAint : Integrable (fun z => F (D.v a z) * parTimeDeriv D.φ z) D.μP := by
    refine Integrable.of_bound (hFmeas.mul htimeMeas) (max MF0 0 * max Mφ 0) ?_
    filter_upwards [hFval, hMφ] with z h1 h2
    rw [Real.norm_eq_abs, abs_mul]
    gcongr
    · exact h2.trans (le_max_left _ _)
  have hDh' : ∀ᵐ z ∂D.μP, |D.Dh a z.1 z.2| ≤ Cflux * D.gG z.2 := by
    rw [D.μP_eq]
    exact ae_prod_of_ae_slice (P := fun x σ => |D.Dh a x σ| ≤ Cflux * D.gG σ) (by
      filter_upwards [hDh] with σ hσ x
      exact hσ x)
  have hBmeas : AEStronglyMeasurable
      (fun z => deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2) D.μP :=
    (hFprimeMeas.mul D.phi_continuous.aestronglyMeasurable).mul
      (D.stronglyMeasurable_Dh a).aestronglyMeasurable
  have hbase : Integrable (fun z : Vec d × ℝ =>
      ((Mderiv : ℝ) * max Mφval 0 * Cflux) * D.gG z.2) D.μP := by
    rw [D.μP_eq]
    exact (integrable_const ((Mderiv : ℝ) * max Mφval 0 * Cflux)).mul_prod D.gG_integrableOn
  have hBint : Integrable
      (fun z => deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2) D.μP := by
    refine hbase.mono' hBmeas ?_
    filter_upwards [hDh', ae_restrict_mem (D.K_measurable.prod measurableSet_Ioc),
      hMφval] with z hz hzmem hφ
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hφ' : |D.φ z| ≤ max Mφval 0 := le_trans hφ (le_max_left _ _)
    calc |deriv F (D.v a z)| * |D.φ z| * |D.Dh a z.1 z.2|
        ≤ ((Mderiv : ℝ) * max Mφval 0) * (Cflux * D.gG z.2) := by
          exact mul_le_mul
            (mul_le_mul (hMderiv _) hφ' (abs_nonneg _) (by positivity)) hz
            (abs_nonneg _) (by positivity)
      _ = ((Mderiv : ℝ) * max Mφval 0 * Cflux) * D.gG z.2 := by ring
  have hsumInt : Integrable
      (fun z => F (D.v a z) * parTimeDeriv D.φ z +
        deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2) D.μP := hAint.add hBint
  have hsumZeroAE : ∀ᵐ x ∂(volume.restrict D.K),
      ∫ τ in Ioc D.s D.t,
        (F (D.v a (x, τ)) * parTimeDeriv D.φ (x, τ) +
          deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ) = 0 := by
    filter_upwards [ae_restrict_mem D.K_measurable] with x hx
    exact time_integral_mollified_zero D ha haδ F hF hFLip hφs hφt hx
  rw [D.μP_eq] at hAint hBint hsumInt ⊢
  have hsumZero : ∫ z,
      F (D.v a z) * parTimeDeriv D.φ z +
        deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2
      ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t))) = 0 := by
    rw [MeasureTheory.integral_prod _ hsumInt]
    apply integral_eq_zero_of_ae
    exact hsumZeroAE
  rw [integral_add hAint hBint] at hsumZero
  exact ⟨hAint, hBint, hsumZero⟩

/-- Nonlinear renormalized integrand at spatial mollification scale `a`.
The flux and gradient are mollified separately; this is the expression whose
limit is the weak renormalized integrand. -/
noncomputable def mollifiedSpatialIntegrand (D : Energy.Data d) (a : ℝ)
    (F : ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  ∑ i, mollT a D.K1 (fun w => D.G w i) z *
    (deriv (deriv F) (D.v a z) * D.φ z *
        mollT a D.K1 (fun w => D.Du w i) z +
      deriv F (D.v a z) * parSpaceGrad D.φ z i)

theorem mollifiedSpatialIntegrand_integrable (D : Energy.Data d) {a : ℝ}
    (ha : 0 < a) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C) :
    Integrable (mollifiedSpatialIntegrand D a F) D.μP := by
  obtain ⟨C1, hC1⟩ := hF'bound
  obtain ⟨C2, hC2⟩ := hF''bound
  obtain ⟨Mφ, hMφ⟩ := D.ae_bound_on_slab D.phi_continuous
  have hF1 := contDiff_deriv_of_two hF
  have hF2cont : Continuous (deriv (deriv F)) := hF1.continuous_deriv (by norm_num)
  have hF'meas : AEStronglyMeasurable (fun z => deriv F (D.v a z)) D.μP := by
    have hcomp : AEStronglyMeasurable (deriv F) (Measure.map (D.v a) D.μP) :=
      hF1.continuous.measurable.aestronglyMeasurable
    exact hcomp.comp_aemeasurable (D.v_aestronglyMeasurable a).aemeasurable
  have hF''meas : AEStronglyMeasurable (fun z => deriv (deriv F) (D.v a z)) D.μP := by
    have hcomp : AEStronglyMeasurable (deriv (deriv F)) (Measure.map (D.v a) D.μP) :=
      hF2cont.measurable.aestronglyMeasurable
    exact hcomp.comp_aemeasurable (D.v_aestronglyMeasurable a).aemeasurable
  have hφmeas : AEStronglyMeasurable D.φ D.μP := D.phi_continuous.aestronglyMeasurable
  have hφbound : ∀ᵐ z ∂D.μP, |D.φ z| ≤ max Mφ 0 := by
    filter_upwards [hMφ] with z hz
    exact hz.trans (le_max_left _ _)
  refine integrable_finsetSum _ fun i _ => ?_
  obtain ⟨Mgrad, hMgrad⟩ := D.ae_bound_on_slab (D.parSpaceGrad_continuous i)
  have hgradmeas : AEStronglyMeasurable (fun z => parSpaceGrad D.φ z i) D.μP :=
    (D.parSpaceGrad_continuous i).aestronglyMeasurable
  have hgradbound : ∀ᵐ z ∂D.μP, |parSpaceGrad D.φ z i| ≤ max Mgrad 0 := by
    filter_upwards [hMgrad] with z hz
    exact hz.trans (le_max_left _ _)
  let w₁ : Vec d × ℝ → ℝ := fun z => deriv (deriv F) (D.v a z) * D.φ z
  let w₂ : Vec d × ℝ → ℝ := fun z => deriv F (D.v a z) * parSpaceGrad D.φ z i
  have hw₁meas : AEStronglyMeasurable w₁ D.μP := by
    exact (hF''meas.mul hφmeas).congr (Eventually.of_forall fun z => rfl)
  have hw₂meas : AEStronglyMeasurable w₂ D.μP := by
    exact (hF'meas.mul hgradmeas).congr (Eventually.of_forall fun z => rfl)
  have hw₁bound : ∀ᵐ z ∂D.μP, |w₁ z| ≤ (C2 : ℝ) * max Mφ 0 := by
    filter_upwards [hφbound] with z hφ
    dsimp [w₁]
    rw [abs_mul]
    exact mul_le_mul (hC2 _) hφ (abs_nonneg _) (by positivity)
  have hw₂bound : ∀ᵐ z ∂D.μP, |w₂ z| ≤ (C1 : ℝ) * max Mgrad 0 := by
    filter_upwards [hgradbound] with z hgrad
    dsimp [w₂]
    rw [abs_mul]
    exact mul_le_mul (hC1 _) hgrad (abs_nonneg _) (by positivity)
  have hpair : Integrable
      (fun z => w₁ z * mollT a D.K1 (fun w => D.G w i) z *
        mollT a D.K1 (fun w => D.Du w i) z) D.μP :=
    integrable_weight_mul hw₁meas hw₁bound (D.memLp_mollG ha i) (D.memLp_mollDu ha i)
  have hflux : Integrable (mollT a D.K1 (fun w => D.G w i)) D.μP :=
    (D.memLp_mollG ha i).integrable (by norm_num)
  have hlinear : Integrable
      (fun z => w₂ z * mollT a D.K1 (fun w => D.G w i) z) D.μP :=
    hflux.bdd_mul hw₂meas (c := (C1 : ℝ) * max Mgrad 0) hw₂bound
  have hterm : Integrable
      (fun z => mollT a D.K1 (fun w => D.G w i) z *
        (w₁ z * mollT a D.K1 (fun w => D.Du w i) z + w₂ z)) D.μP := by
    refine (hpair.add hlinear).congr (Eventually.of_forall fun z => ?_)
    dsimp [w₁, w₂]
    ring
  exact hterm

/-- Spatial integration by parts for a mollified time slice. -/
theorem mollified_spatial_slice_identity (D : Energy.Data d) {a : ℝ}
    (ha : 0 < a) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hφoutside : ∀ x, x ∉ D.K → ∀ τ ∈ Icc D.s D.t, D.φ (x, τ) = 0)
    {τ : ℝ} (hτ : τ ∈ Icc D.s D.t)
    (hGτ : ∀ i, Integrable (fun y => D.G (y, τ) i) (volume.restrict D.K1))
    (hwgτ : ∀ x ∈ D.K, ∀ i,
      ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ) =
        ∫ y in D.K1, kern a (x - y) * D.Du (y, τ) i) :
    (∫ x in D.K, deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ) +
      (∫ x in D.K, mollifiedSpatialIntegrand D a F (x, τ)) = 0 := by
  let γ : Vec d → ℝ := fun x => deriv F (D.v a (x, τ)) * D.φ (x, τ)
  have hF1 := contDiff_deriv_of_two hF
  have hvC : ContDiff ℝ 1 (fun x : Vec d => D.v a (x, τ)) :=
    (D.v_contDiff ha hτ).of_le (by exact_mod_cast le_top)
  have hφC := D.contDiff_phi_slice τ
  have hγC : ContDiff ℝ 1 γ := (hF1.comp hvC).mul hφC
  have hγout : ∀ x, x ∉ D.K → γ x = 0 := by
    intro x hx
    simp [γ, hφoutside x hx τ hτ]
  have hγderiv (x : Vec d) (i : Fin d) :
      fderiv ℝ γ x (basisVec i) =
        deriv (deriv F) (D.v a (x, τ)) *
            fderiv ℝ (fun y => D.v a (y, τ)) x (basisVec i) * D.φ (x, τ) +
          deriv F (D.v a (x, τ)) * parSpaceGrad D.φ (x, τ) i := by
    change fderiv ℝ
        (fun y => deriv F (D.v a (y, τ)) * D.φ (y, τ)) x (basisVec i) = _
    have hmul := vecFDeriv_mul (hF1.comp hvC) hφC x (basisVec i)
    have hmul' :
        fderiv ℝ
            (fun y => deriv F (D.v a (y, τ)) * D.φ (y, τ)) x (basisVec i) =
          fderiv ℝ (fun y => deriv F (D.v a (y, τ))) x (basisVec i) * D.φ (x, τ) +
            deriv F (D.v a (x, τ)) * fderiv ℝ (fun y => D.φ (y, τ)) x (basisVec i) := by
      simpa only [Function.comp_def] using hmul
    have hcomp := vecFDeriv_comp hF1 hvC x (basisVec i)
    have hcomp' :
        fderiv ℝ (fun y => deriv F (D.v a (y, τ))) x (basisVec i) =
          deriv (deriv F) (D.v a (x, τ)) *
            fderiv ℝ (fun y => D.v a (y, τ)) x (basisVec i) := by
      simpa only [Function.comp_def] using hcomp
    rw [hmul', hcomp', D.fderiv_phi_slice τ x i]
  let fi : Fin d → Vec d → ℝ := fun i => D.K1.indicator (fun y => D.G (y, τ) i)
  have hfi : ∀ i, Integrable (fi i) volume := by
    intro i
    exact (integrable_indicator_iff D.K1_measurable).2 (hGτ i)
  have hDhEq (x : Vec d) : D.Dh a x τ =
      ∑ i, fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i) := by
    unfold Energy.Data.Dh
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [moll_fderiv_apply ha (hfi i).locallyIntegrable x (basisVec i),
        ← integral_indicator D.K1_measurable]
      congr 1
      funext y
      by_cases hy : y ∈ D.K1 <;> simp [fi, hy, mul_comm]
    · intro i _
      obtain ⟨C, hC⟩ := kern_fderiv_bound (d := d) ha (basisVec i)
      refine Integrable.mul_bdd (hGτ i) (c := C) ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact ((kern_fderiv_continuous a (basisVec i)).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable
      · simpa using hC (x - y)
  have hconvInt : ∀ i, Integrable
      (fun x => γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i)) volume := by
    intro i
    exact (_root_.PDE.Parabolic.Energy.ibp_moll_integrable ha D.hK hγC hγout (hfi i).locallyIntegrable
      (basisVec i)).1
  have hderivInt : ∀ i, Integrable
      (fun x => fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x) volume := by
    intro i
    exact (_root_.PDE.Parabolic.Energy.ibp_moll_integrable ha D.hK hγC hγout (hfi i).locallyIntegrable
      (basisVec i)).2
  have hγDzero : ∀ x, x ∉ D.K → fderiv ℝ γ x = 0 :=
    fun x hx => fderiv_eq_zero_of_forall_compl D.hK.isClosed hγout hx
  have hspOutside : ∀ x, x ∉ D.K → mollifiedSpatialIntegrand D a F (x, τ) = 0 := by
    intro x hx
    have hφ0 := hφoutside x hx τ hτ
    have hφgrad : parSpaceGrad D.φ (x, τ) = 0 := by
      ext i
      have hfd : fderiv ℝ (fun y : Vec d => D.φ (y, τ)) x = 0 :=
        fderiv_eq_zero_of_forall_compl D.hK.isClosed (fun y hy => hφoutside y hy τ hτ) hx
      rw [← D.fderiv_phi_slice τ x i, hfd]
      simp
    simp [mollifiedSpatialIntegrand, hφ0, hφgrad]
  have hpoint (x : Vec d) (hx : x ∈ D.K) :
      mollifiedSpatialIntegrand D a F (x, τ) =
        ∑ i, fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x := by
    unfold mollifiedSpatialIntegrand γ
    refine Finset.sum_congr rfl fun i _ => ?_
    have hvg := D.fderiv_v_apply ha hτ i (hwgτ x hx i)
    have hbracket :
        deriv (deriv F) (D.v a (x, τ)) * D.φ (x, τ) *
            mollT a D.K1 (fun w => D.Du w i) (x, τ) +
          deriv F (D.v a (x, τ)) * parSpaceGrad D.φ (x, τ) i =
          fderiv ℝ γ x (basisVec i) := by
      calc
        deriv (deriv F) (D.v a (x, τ)) * D.φ (x, τ) *
            mollT a D.K1 (fun w => D.Du w i) (x, τ) +
          deriv F (D.v a (x, τ)) * parSpaceGrad D.φ (x, τ) i =
            deriv (deriv F) (D.v a (x, τ)) *
              mollT a D.K1 (fun w => D.Du w i) (x, τ) * D.φ (x, τ) +
              deriv F (D.v a (x, τ)) * parSpaceGrad D.φ (x, τ) i := by ring
        _ = deriv (deriv F) (D.v a (x, τ)) *
              fderiv ℝ (fun y => D.v a (y, τ)) x (basisVec i) * D.φ (x, τ) +
              deriv F (D.v a (x, τ)) * parSpaceGrad D.φ (x, τ) i := by rw [hvg]
        _ = fderiv ℝ γ x (basisVec i) := (hγderiv x i).symm
    calc
      mollT a D.K1 (fun w => D.G w i) (x, τ) *
          (deriv (deriv F) (D.v a (x, τ)) * D.φ (x, τ) *
            mollT a D.K1 (fun w => D.Du w i) (x, τ) +
            deriv F (D.v a (x, τ)) * parSpaceGrad D.φ (x, τ) i) =
          mollT a D.K1 (fun w => D.G w i) (x, τ) * fderiv ℝ γ x (basisVec i) := by
            rw [hbracket]
      _ = fderiv ℝ γ x (basisVec i) * mollT a D.K1 (fun w => D.G w i) (x, τ) := by ring
      _ = fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x := by rfl
  have hsumInt : Integrable
      (fun x => ∑ i, fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x) volume :=
    integrable_finsetSum _ fun i _ => hderivInt i
  have hwholeL : ∫ x in D.K, γ x * D.Dh a x τ =
      ∫ x, γ x * D.Dh a x τ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hγout x hx]
  have hleft : ∫ x in D.K, γ x * D.Dh a x τ =
      ∫ x, ∑ i, γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i) := by
    rw [hwholeL]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change γ x * D.Dh a x τ =
      ∑ i, γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i)
    rw [hDhEq x, Finset.mul_sum]
  have hleftFin : ∫ x, ∑ i, γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i) =
      ∑ i, ∫ x, γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i) :=
    integral_finsetSum _ fun i _ => hconvInt i
  have hIBP : ∫ x, ∑ i, γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i) =
      -∫ x, ∑ i, fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x := by
    rw [hleftFin, integral_finsetSum _ (fun i _ => hderivInt i),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      _root_.PDE.Parabolic.Energy.ibp_moll ha D.hK hγC hγout
        (hfi i).locallyIntegrable (basisVec i)
  have hright : ∫ x in D.K, mollifiedSpatialIntegrand D a F (x, τ) =
      ∫ x, ∑ i, fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hspOutside]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ D.K
    · exact hpoint x hx
    · change mollifiedSpatialIntegrand D a F (x, τ) =
        ∑ i, fderiv ℝ γ x (basisVec i) * wholeSpaceMollify a (fi i) x
      rw [hspOutside x hx, hγDzero x hx]
      simp
  have hleft' : ∫ x in D.K,
      deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ =
      ∫ x, ∑ i, γ x * fderiv ℝ (wholeSpaceMollify a (fi i)) x (basisVec i) := by
    simpa only [γ] using hleft
  rw [hleft', hIBP, hright]
  simp

noncomputable def mollifiedRenormalizedIntegrand (D : Energy.Data d) (a : ℝ)
    (F : ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  -(F (D.v a z) * parTimeDeriv D.φ z) +
    ∑ i, mollT a D.K1 (fun w => D.G w i) z *
      (deriv (deriv F) (D.v a z) * D.φ z *
          mollT a D.K1 (fun w => D.Du w i) z +
        deriv F (D.v a z) * parSpaceGrad D.φ z i)

/-- At a fixed spatial mollification scale, the weak solution identity and
spatial integration by parts give the renormalized identity. The hypotheses
`hGslice` and `hwg` are precisely the almost-everywhere slice integrability
and weak-gradient statements supplied by `Energy.Data` for a weak solution. -/
theorem mollified_renormalized_integral_zero (D : Energy.Data d) {a : ℝ}
    (ha : 0 < a) (haδ : a ≤ D.δ0) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hFLip : ∃ C : NNReal, LipschitzWith C F)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (hφoutside : ∀ x, x ∉ D.K → ∀ τ ∈ Icc D.s D.t, D.φ (x, τ) = 0)
    (hφs : ∀ x, D.φ (x, D.s) = 0) (hφt : ∀ x, D.φ (x, D.t) = 0)
    (hGslice : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)),
      ∀ i, Integrable (fun y => D.G (y, τ) i) (volume.restrict D.K1))
    (hwg : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)), ∀ x ∈ D.K, ∀ i,
      ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, τ) =
        ∫ y in D.K1, kern a (x - y) * D.Du (y, τ) i) :
    Integrable (mollifiedRenormalizedIntegrand D a F) D.μP ∧
      ∫ z, mollifiedRenormalizedIntegrand D a F z ∂D.μP = 0 := by
  obtain ⟨hAint, hBint, hAB⟩ := temporal_integral_identity D ha haδ F hF hFLip
    hF'bound hφs hφt
  have hSint := mollifiedSpatialIntegrand_integrable D ha F hF hF'bound hF''bound
  have hSlice : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)),
      (∫ x in D.K, deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ) +
        (∫ x in D.K, mollifiedSpatialIntegrand D a F (x, τ)) = 0 := by
    filter_upwards [hGslice, hwg, ae_restrict_mem measurableSet_Ioc] with τ hGτ hwgτ hτ
    exact mollified_spatial_slice_identity D ha F hF hφoutside ⟨hτ.1.le, hτ.2⟩
      hGτ hwgτ
  rw [D.μP_eq] at hAint hBint hSint hAB ⊢
  let μx := volume.restrict D.K
  let μt := volume.restrict (Ioc D.s D.t)
  have hBslice : ∀ᵐ τ ∂μt,
      Integrable (fun x => deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ) μx := by
    exact hBint.prod_left_ae
  have hSslice : ∀ᵐ τ ∂μt,
      Integrable (fun x => mollifiedSpatialIntegrand D a F (x, τ)) μx := by
    exact hSint.prod_left_ae
  have hSlice' : ∀ᵐ τ ∂μt,
      ∫ x, (deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ +
        mollifiedSpatialIntegrand D a F (x, τ)) ∂μx = 0 := by
    filter_upwards [hSlice, hBslice, hSslice] with τ hτ hBτ hSτ
    rw [integral_add hBτ hSτ]
    exact hτ
  have hBSint : Integrable
      (fun z => deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2 +
        mollifiedSpatialIntegrand D a F z) (μx.prod μt) := by
    change Integrable
      ((fun z => deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2) +
        mollifiedSpatialIntegrand D a F) (μx.prod μt)
    exact hBint.add hSint
  have hiter : ∫ τ, ∫ x,
      (deriv F (D.v a (x, τ)) * D.φ (x, τ) * D.Dh a x τ +
        mollifiedSpatialIntegrand D a F (x, τ)) ∂μx ∂μt = 0 :=
    integral_eq_zero_of_ae hSlice'
  have hBSzero : ∫ z,
      (deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2 +
        mollifiedSpatialIntegrand D a F z) ∂(μx.prod μt) = 0 := by
    rw [integral_prod_symm _ hBSint]
    exact hiter
  have hBSzero' :
      (∫ z, deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2 ∂(μx.prod μt)) +
        ∫ z, mollifiedSpatialIntegrand D a F z ∂(μx.prod μt) = 0 := by
    rw [integral_add hBint hSint] at hBSzero
    exact hBSzero
  have hAB' :
      (∫ z, F (D.v a z) * parTimeDeriv D.φ z ∂(μx.prod μt)) +
        ∫ z, deriv F (D.v a z) * D.φ z * D.Dh a z.1 z.2 ∂(μx.prod μt) = 0 := hAB
  have hren :
      -(∫ z, F (D.v a z) * parTimeDeriv D.φ z ∂(μx.prod μt)) +
        ∫ z, mollifiedSpatialIntegrand D a F z ∂(μx.prod μt) = 0 := by
    linarith
  have hfinal : ∫ z, mollifiedRenormalizedIntegrand D a F z ∂(μx.prod μt) = 0 := by
    unfold mollifiedRenormalizedIntegrand
    change (∫ z, -(F (D.v a z) * parTimeDeriv D.φ z) +
      mollifiedSpatialIntegrand D a F z
      ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t)))) = 0
    calc
      _ = -(∫ z, F (D.v a z) * parTimeDeriv D.φ z
          ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t)))) +
          ∫ z, mollifiedSpatialIntegrand D a F z
            ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t))) := by
              calc
                _ = (∫ z, -(F (D.v a z) * parTimeDeriv D.φ z)
                    ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t)))) +
                    ∫ z, mollifiedSpatialIntegrand D a F z
                      ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t))) := by
                        simpa using (integral_add hAint.neg hSint)
                _ = _ := by rw [integral_neg]
      _ = 0 := by simpa [μx, μt] using hren
  constructor
  · exact hAint.neg.add hSint
  · exact hfinal

end PDE.Parabolic.Chain
