/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.CompositionLimit
public import EllipticRegularity.Parabolic.Chain.MeasureLimit
public import EllipticRegularity.Parabolic.Chain.Super.MollifiedInequality

/-! # Passing the nonlinear inequality through the spatial mollification limit -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

/-- The renormalized weak integrand associated to abstract energy data. -/
noncomputable def superRenormalizedIntegrand (D : SuperData d) (F : ℝ → ℝ)
    (z : Vec d × ℝ) : ℝ :=
  -(F (D.u z) * parTimeDeriv D.φ z) +
    ∑ i, (deriv (deriv F) (D.u z) * D.φ z * D.G z i * D.Du z i +
      deriv F (D.u z) * parSpaceGrad D.φ z i * D.G z i)

namespace SuperData

variable (D : SuperData d)

/-- The H¹ limit of the mollified nonlinear inequality. The global bounds on
`F'` and `F''` supply the integrable majorants; continuity of the derivatives
is enough for their coefficients to converge in measure. -/
theorem renormalization_inequality (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hFLip : ∃ C : NNReal, LipschitzWith C F) (hF0 : ∀ r, 0 ≤ deriv F r)
    (hF'bound : ∃ C : NNReal, ∀ s, |deriv F s| ≤ C)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (hφoutside : ∀ x, x ∉ D.K → ∀ τ ∈ Icc D.s D.t, D.φ (x, τ) = 0) :
    Integrable (superRenormalizedIntegrand D F) D.μP ∧
      0 ≤ ∫ z, superRenormalizedIntegrand D F z ∂D.μP := by
  obtain ⟨C1, hC1⟩ := hF'bound
  obtain ⟨C2, hC2⟩ := hF''bound
  let vseq : ℕ → Vec d × ℝ → ℝ := fun n => D.v (D.aSeq n)
  let gseq : ℕ → Fin d → Vec d × ℝ → ℝ := fun n i =>
    mollT (D.aSeq n) D.K1 (fun z => D.G z i)
  let duseq : ℕ → Fin d → Vec d × ℝ → ℝ := fun n i =>
    mollT (D.aSeq n) D.K1 (fun z => D.Du z i)
  let cq : ℕ → Fin d → Vec d × ℝ → ℝ := fun n _ z =>
    deriv (deriv F) (vseq n z) * D.φ z
  let cq0 : Fin d → Vec d × ℝ → ℝ := fun _ z =>
    deriv (deriv F) (D.u z) * D.φ z
  let cl : ℕ → Fin d → Vec d × ℝ → ℝ := fun n i z =>
    deriv F (vseq n z) * parSpaceGrad D.φ z i
  let cl0 : Fin d → Vec d × ℝ → ℝ := fun i z =>
    deriv F (D.u z) * parSpaceGrad D.φ z i
  obtain ⟨Mvφ, hMvφ⟩ := D.ae_bound_on_slab D.phi_continuous
  obtain ⟨Mtime, hMtime⟩ := D.ae_bound_on_slab D.parTimeDeriv_continuous
  let Bφ : ℝ := max Mvφ 0
  let Bt : ℝ := max Mtime 0
  have hBφ : 0 ≤ Bφ := le_max_right _ _
  have hBt : 0 ≤ Bt := le_max_right _ _
  have hφbound : ∀ᵐ z ∂D.μP, |D.φ z| ≤ Bφ := by
    filter_upwards [hMvφ] with z hz
    exact hz.trans (le_max_left _ _)
  have htimebound : ∀ᵐ z ∂D.μP, |parTimeDeriv D.φ z| ≤ Bt := by
    filter_upwards [hMtime] with z hz
    exact hz.trans (le_max_left _ _)
  have hF1 := contDiff_deriv_of_two hF
  have hF2cont : Continuous (deriv (deriv F)) :=
    hF1.continuous_deriv (by norm_num)
  have hF'cont : Continuous (deriv F) := hF1.continuous
  have hvL2 : MemLp D.u 2 D.μP := (D.conv_mollT D.hu2).1
  have hvseqL2 : ∀ n, MemLp (vseq n) 2 D.μP := by
    intro n
    simpa [vseq, SuperData.v] using D.memLp_v (D.aSeq_pos n)
  have hvconv : Tendsto (fun n => eLpNorm (vseq n - D.u) 2 D.μP) atTop (𝓝 0) := by
    simpa [vseq, SuperData.v] using (D.conv_mollT D.hu2).2.2
  have hvmeas : ∀ n, AEStronglyMeasurable (vseq n) D.μP :=
    fun n => by simpa [vseq] using D.v_aestronglyMeasurable (D.aSeq n)
  have hvmeasure : TendstoInMeasure D.μP vseq atTop D.u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hvconv
  have hF'measure : TendstoInMeasure D.μP (fun n z => deriv F (vseq n z)) atTop
      (fun z => deriv F (D.u z)) :=
    tendstoInMeasure_comp_continuous hF'cont hvmeasure hvmeas
  have hF''measure : TendstoInMeasure D.μP (fun n z => deriv (deriv F) (vseq n z)) atTop
      (fun z => deriv (deriv F) (D.u z)) :=
    tendstoInMeasure_comp_continuous hF2cont hvmeasure hvmeas
  have hFcompL2 : ∀ n, MemLp (fun z => F (vseq n z)) 2 D.μP := by
    intro n
    exact memLp_comp_lipschitz hFLip (hvseqL2 n)
  have hFuL2 : MemLp (fun z => F (D.u z)) 2 D.μP :=
    memLp_comp_lipschitz hFLip hvL2
  have hFcompConv : Tendsto
      (fun n => eLpNorm ((fun z => F (vseq n z)) - (fun z => F (D.u z))) 2 D.μP)
      atTop (𝓝 0) := tendsto_eLpNorm_comp_sub_of_lipschitz hFLip hvseqL2 hvL2 hvconv
  have hone : MemLp (fun _ : Vec d × ℝ => (1 : ℝ)) 2 D.μP := memLp_const 1
  have hconstantConv : Tendsto
      (fun _ : ℕ => eLpNorm ((fun _ : Vec d × ℝ => (1 : ℝ)) -
        (fun _ : Vec d × ℝ => (1 : ℝ))) 2 D.μP) atTop (𝓝 0) := by
    simp
  have htimeConv := PDE.Parabolic.Energy.tendsto_integral_weight_mul_of_L2
    D.parTimeDeriv_continuous.aestronglyMeasurable htimebound
    hFcompL2 (fun _ => hone) hFuL2 hone hFcompConv hconstantConv
  have htimeIntegrable : ∀ n, Integrable
      (fun z => parTimeDeriv D.φ z * F (vseq n z) * 1) D.μP := by
    intro n
    exact PDE.Parabolic.Energy.integrable_weight_mul
      D.parTimeDeriv_continuous.aestronglyMeasurable htimebound (hFcompL2 n) hone
  have htimeLimitIntegrable : Integrable
      (fun z => parTimeDeriv D.φ z * F (D.u z) * 1) D.μP :=
    PDE.Parabolic.Energy.integrable_weight_mul
      D.parTimeDeriv_continuous.aestronglyMeasurable htimebound hFuL2 hone
  have htimeTargetIntegrable : Integrable
      (fun z => F (D.u z) * parTimeDeriv D.φ z) D.μP := by
    refine htimeLimitIntegrable.congr (Eventually.of_forall fun z => ?_)
    ring
  have htimeSeqIntegrable (n : ℕ) : Integrable
      (fun z => F (vseq n z) * parTimeDeriv D.φ z) D.μP := by
    refine (htimeIntegrable n).congr (Eventually.of_forall fun z => ?_)
    ring
  have htimeConv' : Tendsto
      (fun n => ∫ z, -(F (vseq n z) * parTimeDeriv D.φ z) ∂D.μP) atTop
      (𝓝 (∫ z, -(F (D.u z) * parTimeDeriv D.φ z) ∂D.μP)) := by
    convert htimeConv.neg using 1
    · funext n
      rw [integral_neg]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      ring
    · rw [integral_neg]
      apply congrArg (fun x : ℝ => 𝓝 (-x))
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      ring
  have hGconv (i : Fin d) := D.conv_mollT (D.hG2 i)
  have hDuconv (i : Fin d) := D.conv_mollT (D.hDu2 i)
  have hQuadConv : ∀ i, Tendsto
      (fun n => ∫ z, cq n i z * gseq n i z * duseq n i z ∂D.μP) atTop
      (𝓝 (∫ z, cq0 i z * D.G z i * D.Du z i ∂D.μP)) := by
    intro i
    have hF2seqMeas : ∀ n, AEStronglyMeasurable
        (fun z => deriv (deriv F) (vseq n z)) D.μP := fun n =>
      hF2cont.measurable.aestronglyMeasurable.comp_aemeasurable (hvmeas n).aemeasurable
    have hF2zeroMeas : AEStronglyMeasurable
        (fun z => deriv (deriv F) (D.u z)) D.μP :=
      hF2cont.measurable.aestronglyMeasurable.comp_aemeasurable hvL2.aestronglyMeasurable.aemeasurable
    have hcMeas : ∀ n, AEStronglyMeasurable (cq n i) D.μP := fun n =>
      (hF2seqMeas n).mul D.phi_continuous.aestronglyMeasurable
    have hc0Meas : AEStronglyMeasurable (cq0 i) D.μP :=
      hF2zeroMeas.mul D.phi_continuous.aestronglyMeasurable
    have hcLim : TendstoInMeasure D.μP (cq · i) atTop (cq0 i) := by
      simpa [cq, cq0] using tendstoInMeasure_mul_fixed hF''measure hF2seqMeas
        D.phi_continuous.aestronglyMeasurable
    have hcBound : ∀ n, ∀ᵐ z ∂D.μP, |cq n i z| ≤ (C2 : ℝ) * Bφ := by
      intro n
      filter_upwards [hφbound] with z hz
      dsimp [cq]
      rw [abs_mul]
      exact mul_le_mul (hC2 _) hz (abs_nonneg _) (by positivity)
    have hc0Bound : ∀ᵐ z ∂D.μP, |cq0 i z| ≤ (C2 : ℝ) * Bφ := by
      filter_upwards [hφbound] with z hz
      dsimp [cq0]
      rw [abs_mul]
      exact mul_le_mul (hC2 _) hz (abs_nonneg _) (by positivity)
    have hgL2 : ∀ n, MemLp (gseq n i) 2 D.μP := fun n => by
      simpa [gseq] using D.memLp_mollG (D.aSeq_pos n) i
    have hduL2 : ∀ n, MemLp (duseq n i) 2 D.μP := fun n => by
      simpa [duseq] using D.memLp_mollDu (D.aSeq_pos n) i
    have hG0L2 : MemLp (D.G · i) 2 D.μP := (D.conv_mollT (D.hG2 i)).1
    have hDu0L2 : MemLp (D.Du · i) 2 D.μP := (D.conv_mollT (D.hDu2 i)).1
    exact tendsto_integral_coeff_mul_product_of_L2 (cq · i) (cq0 i)
      (C := (C2 : ℝ) * Bφ) (by positivity) hcBound hc0Bound hcMeas hc0Meas hcLim
      hgL2 hduL2 hG0L2 hDu0L2
      (by simpa [gseq] using (D.conv_mollT (D.hG2 i)).2.2)
      (by simpa [duseq] using (D.conv_mollT (D.hDu2 i)).2.2)
  have hLinearConv : ∀ i, Tendsto
      (fun n => ∫ z, cl n i z * gseq n i z * 1 ∂D.μP) atTop
      (𝓝 (∫ z, cl0 i z * D.G z i * 1 ∂D.μP)) := by
    intro i
    obtain ⟨Mgrad, hMgrad⟩ := D.ae_bound_on_slab (D.parSpaceGrad_continuous i)
    let Bgrad : ℝ := max Mgrad 0
    have hBgrad : 0 ≤ Bgrad := le_max_right _ _
    have hgradBound : ∀ᵐ z ∂D.μP, |parSpaceGrad D.φ z i| ≤ Bgrad := by
      filter_upwards [hMgrad] with z hz
      exact hz.trans (le_max_left _ _)
    have hF'seqMeas : ∀ n, AEStronglyMeasurable (fun z => deriv F (vseq n z)) D.μP :=
      fun n => hF'cont.measurable.aestronglyMeasurable.comp_aemeasurable
        (hvmeas n).aemeasurable
    have hF'zeroMeas : AEStronglyMeasurable (fun z => deriv F (D.u z)) D.μP :=
      hF'cont.measurable.aestronglyMeasurable.comp_aemeasurable hvL2.aestronglyMeasurable.aemeasurable
    have hcMeas : ∀ n, AEStronglyMeasurable (cl n i) D.μP := fun n =>
      (hF'seqMeas n).mul (D.parSpaceGrad_continuous i).aestronglyMeasurable
    have hc0Meas : AEStronglyMeasurable (cl0 i) D.μP :=
      hF'zeroMeas.mul (D.parSpaceGrad_continuous i).aestronglyMeasurable
    have hcLim : TendstoInMeasure D.μP (cl · i) atTop (cl0 i) := by
      simpa [cl, cl0] using tendstoInMeasure_mul_fixed hF'measure hF'seqMeas
        (D.parSpaceGrad_continuous i).aestronglyMeasurable
    have hcBound : ∀ n, ∀ᵐ z ∂D.μP, |cl n i z| ≤ (C1 : ℝ) * Bgrad := by
      intro n
      filter_upwards [hgradBound] with z hz
      dsimp [cl]
      rw [abs_mul]
      exact mul_le_mul (hC1 _) hz (abs_nonneg _) (by positivity)
    have hc0Bound : ∀ᵐ z ∂D.μP, |cl0 i z| ≤ (C1 : ℝ) * Bgrad := by
      filter_upwards [hgradBound] with z hz
      dsimp [cl0]
      rw [abs_mul]
      exact mul_le_mul (hC1 _) hz (abs_nonneg _) (by positivity)
    have hgL2 : ∀ n, MemLp (gseq n i) 2 D.μP := fun n => by
      simpa [gseq] using D.memLp_mollG (D.aSeq_pos n) i
    have hG0L2 : MemLp (D.G · i) 2 D.μP := (D.conv_mollT (D.hG2 i)).1
    exact tendsto_integral_coeff_mul_product_of_L2 (cl · i) (cl0 i)
      (C := (C1 : ℝ) * Bgrad) (by positivity) hcBound hc0Bound hcMeas hc0Meas hcLim
      hgL2 (fun _ => hone) hG0L2 hone
      (by simpa [gseq] using (D.conv_mollT (D.hG2 i)).2.2)
      (by simp)
  have hsumConv := tendsto_finsetSum Finset.univ fun i _ =>
    (hQuadConv i).add (hLinearConv i)
  have hquadInt : ∀ n i, Integrable (fun z => cq n i z * gseq n i z * duseq n i z) D.μP := by
    intro n i
    have hm : AEStronglyMeasurable (cq n i) D.μP := by
      have hc := hF2cont.measurable.aestronglyMeasurable.comp_aemeasurable (hvmeas n).aemeasurable
      exact hc.mul D.phi_continuous.aestronglyMeasurable
    have hb : ∀ᵐ z ∂D.μP, |cq n i z| ≤ (C2 : ℝ) * Bφ := by
      filter_upwards [hφbound] with z hz
      dsimp [cq]
      rw [abs_mul]
      exact mul_le_mul (hC2 _) hz (abs_nonneg _) (by positivity)
    exact PDE.Parabolic.Energy.integrable_weight_mul hm hb
      (D.memLp_mollG (D.aSeq_pos n) i) (D.memLp_mollDu (D.aSeq_pos n) i)
  have hlinearInt : ∀ n i, Integrable (fun z => cl n i z * gseq n i z * 1) D.μP := by
    intro n i
    obtain ⟨Mgrad, hMgrad⟩ := D.ae_bound_on_slab (D.parSpaceGrad_continuous i)
    have hm : AEStronglyMeasurable (cl n i) D.μP := by
      exact (hF'cont.measurable.aestronglyMeasurable.comp_aemeasurable
        (hvmeas n).aemeasurable).mul (D.parSpaceGrad_continuous i).aestronglyMeasurable
    have hb : ∀ᵐ z ∂D.μP, |cl n i z| ≤ (C1 : ℝ) * max Mgrad 0 := by
      filter_upwards [hMgrad] with z hz
      dsimp [cl]
      rw [abs_mul]
      exact mul_le_mul (hC1 _) (hz.trans (le_max_left _ _)) (abs_nonneg _) (by positivity)
    exact PDE.Parabolic.Energy.integrable_weight_mul hm hb
      (D.memLp_mollG (D.aSeq_pos n) i) hone
  have hquad0Int : ∀ i, Integrable (fun z => cq0 i z * D.G z i * D.Du z i) D.μP := by
    intro i
    have hm := (hF2cont.measurable.aestronglyMeasurable.comp_aemeasurable
      hvL2.aestronglyMeasurable.aemeasurable).mul D.phi_continuous.aestronglyMeasurable
    have hb : ∀ᵐ z ∂D.μP, |cq0 i z| ≤ (C2 : ℝ) * Bφ := by
      filter_upwards [hφbound] with z hz
      dsimp [cq0]
      rw [abs_mul]
      exact mul_le_mul (hC2 _) hz (abs_nonneg _) (by positivity)
    exact PDE.Parabolic.Energy.integrable_weight_mul hm hb (D.memLp_G i) (D.memLp_Du i)
  have hlinear0Int : ∀ i, Integrable (fun z => cl0 i z * D.G z i * 1) D.μP := by
    intro i
    obtain ⟨Mgrad, hMgrad⟩ := D.ae_bound_on_slab (D.parSpaceGrad_continuous i)
    have hm := (hF'cont.measurable.aestronglyMeasurable.comp_aemeasurable
      hvL2.aestronglyMeasurable.aemeasurable).mul
        (D.parSpaceGrad_continuous i).aestronglyMeasurable
    have hb : ∀ᵐ z ∂D.μP, |cl0 i z| ≤ (C1 : ℝ) * max Mgrad 0 := by
      filter_upwards [hMgrad] with z hz
      dsimp [cl0]
      rw [abs_mul]
      exact mul_le_mul (hC1 _) (hz.trans (le_max_left _ _)) (abs_nonneg _) (by positivity)
    exact PDE.Parabolic.Energy.integrable_weight_mul hm hb (D.memLp_G i) hone
  have htempSum (n : ℕ) : Integrable (fun z => ∑ i,
      (gseq n i z * (deriv (deriv F) (vseq n z) * D.φ z * duseq n i z +
        deriv F (vseq n z) * parSpaceGrad D.φ z i))) D.μP := by
    apply integrable_finsetSum
    intro i hi
    refine ((hquadInt n i).add (hlinearInt n i)).congr
      (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, cq, cl, gseq, duseq]
    ring
  have hlimSum : Integrable (fun z => ∑ i,
      (cq0 i z * D.G z i * D.Du z i + cl0 i z * D.G z i * 1)) D.μP := by
    exact integrable_finsetSum _ fun i _ => (hquad0Int i).add (hlinear0Int i)
  have hlimSumExact : Integrable (fun z => ∑ i,
      (deriv (deriv F) (D.u z) * D.φ z * D.G z i * D.Du z i +
        deriv F (D.u z) * parSpaceGrad D.φ z i * D.G z i)) D.μP := by
    refine hlimSum.congr (Eventually.of_forall fun z => ?_)
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [cq0, cl0]
    ring
  have hterm0 (i : Fin d) : Integrable
      (fun z => cq0 i z * D.G z i * D.Du z i + cl0 i z * D.G z i * 1) D.μP :=
    (hquad0Int i).add (hlinear0Int i)
  have hsplitTarget : ∫ z, superRenormalizedIntegrand D F z ∂D.μP =
      (∫ z, -(F (D.u z) * parTimeDeriv D.φ z) ∂D.μP) +
        ∑ i, (∫ z, cq0 i z * D.G z i * D.Du z i ∂D.μP +
          ∫ z, cl0 i z * D.G z i * 1 ∂D.μP) := by
    unfold superRenormalizedIntegrand
    calc
      _ = (∫ z, -(F (D.u z) * parTimeDeriv D.φ z) ∂D.μP) +
          ∫ z, ∑ i, (deriv (deriv F) (D.u z) * D.φ z * D.G z i * D.Du z i +
            deriv F (D.u z) * parSpaceGrad D.φ z i * D.G z i) ∂D.μP :=
        integral_add htimeTargetIntegrable.neg hlimSumExact
      _ = _ := by
        rw [integral_finsetSum _ fun i _ => by
          refine (hterm0 i).congr (Eventually.of_forall fun z => ?_)
          dsimp [cq0, cl0]
          ring]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∫ z, (cq0 i z * D.G z i * D.Du z i + cl0 i z * D.G z i * 1) ∂D.μP := by
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            dsimp [cq0, cl0]
            ring
          _ = (∫ z, cq0 i z * D.G z i * D.Du z i ∂D.μP) +
              ∫ z, cl0 i z * D.G z i * 1 ∂D.μP :=
            integral_add (hquad0Int i) (hlinear0Int i)
  have hsplitMoll (n : ℕ) :
      ∫ z, mollifiedRenormalizedIntegrand D (D.aSeq n) F z ∂D.μP =
        (∫ z, -(F (vseq n z) * parTimeDeriv D.φ z) ∂D.μP) +
          ∑ i, (∫ z, cq n i z * gseq n i z * duseq n i z ∂D.μP +
            ∫ z, cl n i z * gseq n i z * 1 ∂D.μP) := by
    have htermM (i : Fin d) : Integrable
        (fun z => gseq n i z * (deriv (deriv F) (vseq n z) * D.φ z * duseq n i z +
          deriv F (vseq n z) * parSpaceGrad D.φ z i)) D.μP := by
      refine ((hquadInt n i).add (hlinearInt n i)).congr
        (Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, cq, cl, gseq, duseq]
      ring
    calc
      _ = ∫ z, (-(F (vseq n z) * parTimeDeriv D.φ z) +
          ∑ i, gseq n i z * (deriv (deriv F) (vseq n z) * D.φ z * duseq n i z +
            deriv F (vseq n z) * parSpaceGrad D.φ z i)) ∂D.μP := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp [mollifiedRenormalizedIntegrand, vseq, gseq, duseq,
          SuperData.v]
      _ = (∫ z, -(F (vseq n z) * parTimeDeriv D.φ z) ∂D.μP) +
          ∫ z, ∑ i, gseq n i z * (deriv (deriv F) (vseq n z) * D.φ z * duseq n i z +
            deriv F (vseq n z) * parSpaceGrad D.φ z i) ∂D.μP :=
        integral_add (htimeSeqIntegrable n).neg (htempSum n)
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => htermM i)]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∫ z, (cq n i z * gseq n i z * duseq n i z +
              cl n i z * gseq n i z * 1) ∂D.μP := by
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            dsimp [cq, cl, gseq, duseq, vseq]
            ring
          _ = (∫ z, cq n i z * gseq n i z * duseq n i z ∂D.μP) +
              ∫ z, cl n i z * gseq n i z * 1 ∂D.μP :=
            integral_add (hquadInt n i) (hlinearInt n i)
  have hrenormalizedLimit : Tendsto
      (fun n => (∫ z, -(F (vseq n z) * parTimeDeriv D.φ z) ∂D.μP) +
        ∑ i, (∫ z, cq n i z * gseq n i z * duseq n i z ∂D.μP +
          ∫ z, cl n i z * gseq n i z * 1 ∂D.μP)) atTop
      (𝓝 ((∫ z, -(F (D.u z) * parTimeDeriv D.φ z) ∂D.μP) +
        ∑ i, (∫ z, cq0 i z * D.G z i * D.Du z i ∂D.μP +
          ∫ z, cl0 i z * D.G z i * 1 ∂D.μP))) := by
    exact htimeConv'.add hsumConv
  have hmoll (n : ℕ) :
      0 ≤ ∫ z, mollifiedRenormalizedIntegrand D (D.aSeq n) F z ∂D.μP := by
    have hGslice : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)),
        ∀ i, Integrable (fun y => D.G (y, τ) i) (volume.restrict D.K1) := by
      rw [ae_all_iff]
      intro i
      have hprod : Integrable (fun z => D.G z i)
          ((volume.restrict D.K1).prod (volume.restrict (Ioc D.s D.t))) := by
        rw [← volume_restrict_prod]
        exact (D.hG2 i).integrable (by norm_num)
      exact hprod.prod_left_ae
    have hwg : ∀ᵐ τ ∂(volume.restrict (Ioc D.s D.t)), ∀ x ∈ D.K, ∀ i,
        ∫ y in D.K1, fderiv ℝ (kern (D.aSeq n)) (x - y) (basisVec i) * D.u (y, τ) =
          ∫ y in D.K1, kern (D.aSeq n) (x - y) * D.Du (y, τ) i := by
      filter_upwards [D.hwg] with τ hτ
      exact hτ (D.aSeq n) (D.aSeq_pos n) (D.aSeq_le_δ0 n)
    exact (mollified_renormalized_integral_nonneg D (D.aSeq_pos n) (D.aSeq_le_δ0 n)
      F hF hF0 ⟨C1, hC1⟩ ⟨C2, hC2⟩ hφoutside hGslice hwg).2
  have hseq : Tendsto
      (fun n => ∫ z, mollifiedRenormalizedIntegrand D (D.aSeq n) F z ∂D.μP) atTop
      (𝓝 (∫ z, superRenormalizedIntegrand D F z ∂D.μP)) := by
    simpa only [hsplitMoll, hsplitTarget] using hrenormalizedLimit
  have hnonneg : 0 ≤ ∫ z, superRenormalizedIntegrand D F z ∂D.μP :=
    ge_of_tendsto hseq (Eventually.of_forall hmoll)
  exact ⟨htimeTargetIntegrable.neg.add hlimSumExact, hnonneg⟩

end SuperData

end PDE.Parabolic.Chain.Super
