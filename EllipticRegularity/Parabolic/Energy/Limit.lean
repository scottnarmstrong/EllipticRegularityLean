module

public import EllipticRegularity.Parabolic.Energy.Mollified

/-!
# The limit `δ → 0` in the energy identity
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

/-- The scale sequence `δ0 / (n + 1)`. -/
noncomputable def aSeq (n : ℕ) : ℝ := D.δ0 / ((n : ℝ) + 1)

theorem aSeq_pos (n : ℕ) : 0 < D.aSeq n := by unfold aSeq; have := D.hδ0; positivity

theorem aSeq_le_δ0 (n : ℕ) : D.aSeq n ≤ D.δ0 := by
  unfold aSeq
  rw [div_le_iff₀ (by positivity)]
  nlinarith [D.hδ0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem aSeq_le_one (n : ℕ) : D.aSeq n ≤ 1 := (D.aSeq_le_δ0 n).trans D.hδ1

theorem aSeq_tendsto : Tendsto D.aSeq atTop (𝓝 0) := by
  unfold aSeq
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul D.δ0
  simpa [div_eq_mul_inv] using this

/-- Convergence of the slice-wise mollifications of an `L²` function on the slab. -/
theorem conv_mollT {g : Vec d × ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (D.K1 ×ˢ Ioc D.s D.t))) :
    MemLp g 2 D.μP ∧ (∀ n, MemLp (mollT (D.aSeq n) D.K1 g) 2 D.μP) ∧
      Tendsto (fun n => eLpNorm (mollT (D.aSeq n) D.K1 g - g) 2 D.μP) atTop (𝓝 0) := by
  have hg' : MemLp g 2 D.μP :=
    hg.mono_measure (Measure.restrict_mono (prod_mono D.K_subset_K1 subset_rfl) le_rfl)
  refine ⟨hg', fun n => memLp_mollT D.K1_compact hg (D.aSeq_pos n), ?_⟩
  refine tendsto_eLpNorm_sub_of_lintegral
    (fun n => aestronglyMeasurable_mollT D.K1_measurable D.K hg.aestronglyMeasurable _)
    hg'.aestronglyMeasurable ?_
  exact tendsto_lintegral_mollT D.K1_compact D.K_subset_K1 D.K_measurable hg D.aSeq_pos
    D.aSeq_le_one D.aSeq_tendsto

theorem tendsto_fixed_time {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    Tendsto (fun n => ∫ x in D.K, D.φ (x, τ) ^ 2 * D.v (D.aSeq n) (x, τ) ^ 2) atTop
      (𝓝 (∫ x in D.K, D.φ (x, τ) ^ 2 * D.u (x, τ) ^ 2)) := by
  set f := D.K1.indicator fun y => D.u (y, τ) with hf
  have hfL2 : MemLp f 2 volume := D.slice_memLp hτ
  have hφc : Continuous fun x => D.φ (x, τ) ^ 2 :=
    (D.phi_continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  obtain ⟨M, hM⟩ := D.hK.exists_bound_of_continuousOn hφc.continuousOn
  have hMae : ∀ᵐ x ∂(volume.restrict D.K), |D.φ (x, τ) ^ 2| ≤ M :=
    (ae_restrict_iff' D.K_measurable).2 (Filter.Eventually.of_forall fun x hx => by
      simpa using hM x hx)
  have hG : ∀ n, MemLp (fun x => D.v (D.aSeq n) (x, τ)) 2 (volume.restrict D.K) := fun n =>
    (eLpNorm_moll_le (D.aSeq_pos n) hfL2).1.mono_measure Measure.restrict_le_self
  have hG0 : MemLp (fun x => D.u (x, τ)) 2 (volume.restrict D.K) :=
    (D.hus τ hτ).mono_measure (Measure.restrict_mono D.K_subset_K1 le_rfl)
  have hl : Tendsto (fun n => eLpNorm ((fun x => D.v (D.aSeq n) (x, τ)) - fun x => D.u (x, τ)) 2
      (volume.restrict D.K)) atTop (𝓝 0) := by
    have h1 := tendsto_eLpNorm_wholeSpaceMollify_sub (p := 2) (by norm_num) (by norm_num) hfL2
      D.aSeq_pos D.aSeq_le_one D.aSeq_tendsto
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => bot_le)
      (fun n => ?_)
    have hae : ((fun x => D.v (D.aSeq n) (x, τ)) - fun x => D.u (x, τ)) =ᵐ[volume.restrict D.K]
        (wholeSpaceMollify (D.aSeq n) f - f) := by
      filter_upwards [ae_restrict_mem D.K_measurable] with x hx
      simp only [Pi.sub_apply]
      rw [hf, Set.indicator_of_mem (D.K_subset_K1 hx)]
      rfl
    rw [eLpNorm_congr_ae hae]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have := tendsto_integral_weight_mul_of_L2 (hφc.aestronglyMeasurable) hMae hG hG hG0 hG0 hl hl
  have e1 : ∀ n, ∫ x, D.φ (x, τ) ^ 2 * D.v (D.aSeq n) (x, τ) * D.v (D.aSeq n) (x, τ)
        ∂(volume.restrict D.K) = ∫ x in D.K, D.φ (x, τ) ^ 2 * D.v (D.aSeq n) (x, τ) ^ 2 := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e0 : ∫ x, D.φ (x, τ) ^ 2 * D.u (x, τ) * D.u (x, τ) ∂(volume.restrict D.K) =
      ∫ x in D.K, D.φ (x, τ) ^ 2 * D.u (x, τ) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [e0] at this
  exact this.congr e1

theorem tendsto_H1 :
    Tendsto (fun n => ∫ z, D.H1 (D.aSeq n) z ∂D.μP) atTop
      (𝓝 (∫ z, D.u z ^ 2 * D.φ z * parTimeDeriv D.φ z ∂D.μP)) := by
  obtain ⟨hu0, hun, hul⟩ := D.conv_mollT D.hu2
  have hw : Continuous fun z : Vec d × ℝ => D.φ z * parTimeDeriv D.φ z :=
    D.phi_continuous.mul D.parTimeDeriv_continuous
  obtain ⟨M, hM⟩ := D.ae_bound_on_slab hw
  have hu' : ∀ n, D.v (D.aSeq n) = mollT (D.aSeq n) D.K1 D.u := fun n => rfl
  have := tendsto_integral_weight_mul_of_L2 hw.aestronglyMeasurable hM
    (F := fun n => mollT (D.aSeq n) D.K1 D.u) (G := fun n => mollT (D.aSeq n) D.K1 D.u)
    hun hun hu0 hu0 hul hul
  have e1 : ∀ n, ∫ z, D.φ z * parTimeDeriv D.φ z * mollT (D.aSeq n) D.K1 D.u z *
      mollT (D.aSeq n) D.K1 D.u z ∂D.μP = ∫ z, D.H1 (D.aSeq n) z ∂D.μP := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [H1, v]
    ring
  have e0 : ∫ z, D.φ z * parTimeDeriv D.φ z * D.u z * D.u z ∂D.μP =
      ∫ z, D.u z ^ 2 * D.φ z * parTimeDeriv D.φ z ∂D.μP := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [e0] at this
  exact this.congr e1

theorem tendsto_S :
    Tendsto (fun n => ∫ z, D.S (D.aSeq n) z ∂D.μP) atTop
      (𝓝 (∫ z, ∑ i, D.G z i * (D.φ z ^ 2 * D.Du z i + 2 * D.φ z * D.u z * parSpaceGrad D.φ z i)
        ∂D.μP)) := by
  obtain ⟨hu0, hun, hul⟩ := D.conv_mollT D.hu2
  have hw1 : Continuous fun z : Vec d × ℝ => D.φ z ^ 2 := D.phi_continuous.pow 2
  have hw2 : ∀ i, Continuous fun z : Vec d × ℝ => 2 * D.φ z * parSpaceGrad D.φ z i := fun i =>
    (continuous_const.mul D.phi_continuous).mul (D.parSpaceGrad_continuous i)
  obtain ⟨M1, hM1⟩ := D.ae_bound_on_slab hw1
  have hM2 := fun i => (D.ae_bound_on_slab (hw2 i))
  choose M2 hM2 using hM2
  -- limits of each term
  have L1 : ∀ i, Tendsto (fun n => ∫ z, D.φ z ^ 2 * mollT (D.aSeq n) D.K1 (fun z => D.G z i) z *
      mollT (D.aSeq n) D.K1 (fun z => D.Du z i) z ∂D.μP) atTop
      (𝓝 (∫ z, D.φ z ^ 2 * D.G z i * D.Du z i ∂D.μP)) := by
    intro i
    obtain ⟨hG0, hGn, hGl⟩ := D.conv_mollT (D.hG2 i)
    obtain ⟨hD0, hDn, hDl⟩ := D.conv_mollT (D.hDu2 i)
    exact tendsto_integral_weight_mul_of_L2 hw1.aestronglyMeasurable hM1 hGn hDn hG0 hD0 hGl hDl
  have L2 : ∀ i, Tendsto (fun n => ∫ z, (2 * D.φ z * parSpaceGrad D.φ z i) *
      mollT (D.aSeq n) D.K1 (fun z => D.G z i) z * mollT (D.aSeq n) D.K1 D.u z ∂D.μP) atTop
      (𝓝 (∫ z, (2 * D.φ z * parSpaceGrad D.φ z i) * D.G z i * D.u z ∂D.μP)) := by
    intro i
    obtain ⟨hG0, hGn, hGl⟩ := D.conv_mollT (D.hG2 i)
    exact tendsto_integral_weight_mul_of_L2 (hw2 i).aestronglyMeasurable (hM2 i) hGn hun hG0 hu0
      hGl hul
  have hsum := tendsto_finsetSum Finset.univ fun i _ => (L1 i).add (L2 i)
  -- integrability of the terms
  have I1 : ∀ n i, Integrable (fun z => D.φ z ^ 2 * mollT (D.aSeq n) D.K1 (fun z => D.G z i) z *
      mollT (D.aSeq n) D.K1 (fun z => D.Du z i) z) D.μP := fun n i =>
    integrable_weight_mul hw1.aestronglyMeasurable hM1 (D.memLp_mollG (D.aSeq_pos n) i)
      (D.memLp_mollDu (D.aSeq_pos n) i)
  have I2 : ∀ n i, Integrable (fun z => (2 * D.φ z * parSpaceGrad D.φ z i) *
      mollT (D.aSeq n) D.K1 (fun z => D.G z i) z * mollT (D.aSeq n) D.K1 D.u z) D.μP :=
    fun n i => integrable_weight_mul (hw2 i).aestronglyMeasurable (hM2 i)
      (D.memLp_mollG (D.aSeq_pos n) i) (D.memLp_v (D.aSeq_pos n))
  have J1 : ∀ i, Integrable (fun z => D.φ z ^ 2 * D.G z i * D.Du z i) D.μP := fun i =>
    integrable_weight_mul hw1.aestronglyMeasurable hM1 (D.conv_mollT (D.hG2 i)).1
      (D.conv_mollT (D.hDu2 i)).1
  have J2 : ∀ i, Integrable (fun z => (2 * D.φ z * parSpaceGrad D.φ z i) * D.G z i * D.u z) D.μP :=
    fun i => integrable_weight_mul (hw2 i).aestronglyMeasurable (hM2 i)
      (D.conv_mollT (D.hG2 i)).1 hu0
  have e1 : ∀ n, ∫ z, D.S (D.aSeq n) z ∂D.μP =
      ∑ i, (∫ z, D.φ z ^ 2 * mollT (D.aSeq n) D.K1 (fun z => D.G z i) z *
        mollT (D.aSeq n) D.K1 (fun z => D.Du z i) z ∂D.μP +
      ∫ z, (2 * D.φ z * parSpaceGrad D.φ z i) *
        mollT (D.aSeq n) D.K1 (fun z => D.G z i) z * mollT (D.aSeq n) D.K1 D.u z ∂D.μP) := by
    intro n
    calc ∫ z, D.S (D.aSeq n) z ∂D.μP
        = ∫ z, ∑ i, (D.φ z ^ 2 * mollT (D.aSeq n) D.K1 (fun z => D.G z i) z *
            mollT (D.aSeq n) D.K1 (fun z => D.Du z i) z +
          (2 * D.φ z * parSpaceGrad D.φ z i) *
            mollT (D.aSeq n) D.K1 (fun z => D.G z i) z * mollT (D.aSeq n) D.K1 D.u z) ∂D.μP := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [S, v]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∫ z, (D.φ z ^ 2 * mollT (D.aSeq n) D.K1 (fun z => D.G z i) z *
            mollT (D.aSeq n) D.K1 (fun z => D.Du z i) z +
          (2 * D.φ z * parSpaceGrad D.φ z i) *
            mollT (D.aSeq n) D.K1 (fun z => D.G z i) z * mollT (D.aSeq n) D.K1 D.u z) ∂D.μP :=
          integral_finsetSum _ fun i _ => (I1 n i).add (I2 n i)
      _ = _ := Finset.sum_congr rfl fun i _ => integral_add (I1 n i) (I2 n i)
  have e0 : ∫ z, ∑ i, D.G z i * (D.φ z ^ 2 * D.Du z i + 2 * D.φ z * D.u z * parSpaceGrad D.φ z i)
        ∂D.μP =
      ∑ i, (∫ z, D.φ z ^ 2 * D.G z i * D.Du z i ∂D.μP +
        ∫ z, (2 * D.φ z * parSpaceGrad D.φ z i) * D.G z i * D.u z ∂D.μP) := by
    calc ∫ z, ∑ i, D.G z i * (D.φ z ^ 2 * D.Du z i + 2 * D.φ z * D.u z * parSpaceGrad D.φ z i)
          ∂D.μP
        = ∫ z, ∑ i, (D.φ z ^ 2 * D.G z i * D.Du z i +
            (2 * D.φ z * parSpaceGrad D.φ z i) * D.G z i * D.u z) ∂D.μP := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∫ z, (D.φ z ^ 2 * D.G z i * D.Du z i +
            (2 * D.φ z * parSpaceGrad D.φ z i) * D.G z i * D.u z) ∂D.μP :=
          integral_finsetSum _ fun i _ => (J1 i).add (J2 i)
      _ = _ := Finset.sum_congr rfl fun i _ => integral_add (J1 i) (J2 i)
  rw [e0]
  exact hsum.congr fun n => (e1 n).symm

/-- The abstract energy identity. -/
theorem energy_identity :
    (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) ^ 2) =
      (∫ z, D.u z ^ 2 * D.φ z * parTimeDeriv D.φ z ∂D.μP) -
        ∫ z, ∑ i, D.G z i * (D.φ z ^ 2 * D.Du z i + 2 * D.φ z * D.u z * parSpaceGrad D.φ z i)
          ∂D.μP := by
  have ht : D.t ∈ Icc D.s D.t := ⟨D.hst.le, le_rfl⟩
  have hs : D.s ∈ Icc D.s D.t := ⟨le_rfl, D.hst.le⟩
  have hL := ((D.tendsto_fixed_time ht).const_mul (1 / 2 : ℝ)).sub
    ((D.tendsto_fixed_time hs).const_mul (1 / 2 : ℝ))
  have hR := D.tendsto_H1.sub D.tendsto_S
  refine tendsto_nhds_unique (hL.congr fun n => ?_) hR
  exact (D.energy_mollified (D.aSeq_pos n) (D.aSeq_le_δ0 n)).symm ▸ rfl

end Data

end PDE.Parabolic.Energy
