/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.Super.SuperData

/-! # Measurability, integrability and mollifier calculus for `SuperData` -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Chain.Super

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

namespace SuperData

variable (D : SuperData d)

/-- The space-time measure on `K × (s,t]`. -/
noncomputable abbrev μP : Measure (Vec d × ℝ) := volume.restrict (D.K ×ˢ Ioc D.s D.t)

theorem μP_eq : D.μP = (volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t)) :=
  volume_restrict_prod _ _

instance : IsFiniteMeasure D.μP :=
  ⟨by
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top D.hK.measure_lt_top (by simp)⟩

instance : IsFiniteMeasure (volume.restrict D.K) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact D.hK.measure_lt_top⟩

theorem phi_continuous : Continuous D.φ := D.hφ.continuous

theorem parTimeDeriv_continuous : Continuous (parTimeDeriv D.φ) :=
  (D.hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem parSpaceGrad_continuous (i : Fin d) : Continuous fun z => parSpaceGrad D.φ z i :=
  (D.hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem bound_on_slab {f : Vec d × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, ∀ z ∈ D.K ×ˢ Icc D.s D.t, |f z| ≤ M := by
  obtain ⟨M, hM⟩ := (D.hK.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun z hz => by simpa using hM z hz⟩

theorem ae_bound_on_slab {f : Vec d × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, ∀ᵐ z ∂D.μP, |f z| ≤ M := by
  obtain ⟨M, hM⟩ := D.bound_on_slab hf
  refine ⟨M, ?_⟩
  exact (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioc)).2
    (Filter.Eventually.of_forall fun z hz => hM z ⟨hz.1, Ioc_subset_Icc_self hz.2⟩)

theorem stronglyMeasurable_Dh (a : ℝ) :
    StronglyMeasurable fun z : Vec d × ℝ => D.Dh a z.1 z.2 := by
  have hF : Measurable fun p : (Vec d × ℝ) × Vec d =>
      ∑ i, D.G (p.2, p.1.2) i * fderiv ℝ (kern a) (p.1.1 - p.2) (basisVec i) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.mul ?_ ?_
    · exact (D.hGm i).comp (measurable_snd.prodMk measurable_fst.snd)
    · exact (kern_fderiv_continuous a (basisVec i)).measurable.comp
        (measurable_fst.fst.sub measurable_snd)
  have := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict D.K1)
  exact this

theorem v_aestronglyMeasurable (a : ℝ) : AEStronglyMeasurable (D.v a) D.μP :=
  aestronglyMeasurable_mollT D.K1_measurable D.K D.hu2.aestronglyMeasurable a

theorem ae_v_bound {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    ∃ B : ℝ, ∀ᵐ z ∂D.μP, |D.v a z| ≤ B := by
  obtain ⟨B, hB⟩ := D.exists_v_bound ha haδ
  exact ⟨B, (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioc)).2
    (Filter.Eventually.of_forall fun z hz => hB z.1 hz.1 z.2 ⟨hz.2.1.le, hz.2.2⟩)⟩

theorem slice_memLp {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    MemLp (D.K1.indicator fun y => D.u (y, τ)) 2 volume :=
  (memLp_indicator_iff_restrict D.K1_measurable).2 (D.hus τ hτ)

theorem v_contDiff {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => D.v a (x, τ) :=
  moll_contDiff ha ((D.slice_memLp hτ).locallyIntegrable (by norm_num))

theorem memLp_mollG {a : ℝ} (ha : 0 < a) (i : Fin d) :
    MemLp (mollT a D.K1 fun z => D.G z i) 2 D.μP :=
  memLp_mollT D.K1_compact (D.hG2 i) ha

theorem memLp_mollDu {a : ℝ} (ha : 0 < a) (i : Fin d) :
    MemLp (mollT a D.K1 fun z => D.Du z i) 2 D.μP :=
  memLp_mollT D.K1_compact (D.hDu2 i) ha

theorem memLp_v {a : ℝ} (ha : 0 < a) : MemLp (D.v a) 2 D.μP :=
  memLp_mollT D.K1_compact D.hu2 ha

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

theorem memLp_u : MemLp D.u 2 D.μP := (D.conv_mollT D.hu2).1

theorem memLp_Du (i : Fin d) : MemLp (fun z => D.Du z i) 2 D.μP := (D.conv_mollT (D.hDu2 i)).1

theorem memLp_G (i : Fin d) : MemLp (fun z => D.G z i) 2 D.μP := (D.conv_mollT (D.hG2 i)).1

theorem mem_cthickening_two {a : ℝ} (haδ : a ≤ D.δ0) {x y : Vec d} (hy : y ∈ D.K1)
    (hxy : ‖x - y‖ ≤ a) : x ∈ cthickening (2 * D.δ0) D.K := by
  have hy' : y ∈ ⋃ p ∈ D.K, closedBall p D.δ0 := by
    rw [← D.hK.cthickening_eq_biUnion_closedBall D.hδ0.le]; exact hy
  simp only [mem_iUnion] at hy'
  obtain ⟨p, hp, hyp⟩ := hy'
  refine mem_cthickening_of_dist_le x p (2 * D.δ0) D.K hp ?_
  calc dist x p ≤ dist x y + dist y p := dist_triangle _ _ _
    _ ≤ a + D.δ0 := add_le_add (by rwa [dist_eq_norm]) (by simpa using hyp)
    _ ≤ 2 * D.δ0 := by linarith

theorem v_eq_zero_of_far {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {x : Vec d}
    (hx : x ∉ cthickening (2 * D.δ0) D.K) (τ : ℝ) : D.v a (x, τ) = 0 := by
  unfold v mollT
  refine moll_eq_zero ha fun y hy => ?_
  have : y ∉ D.K1 := fun hyK => hx (D.mem_cthickening_two haδ hyK hy)
  simp [this]

theorem fderiv_phi_slice (σ : ℝ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun x => D.φ (x, σ)) x (basisVec i) = parSpaceGrad D.φ (x, σ) i := by
  have h1 : HasFDerivAt D.φ (fderiv ℝ D.φ (x, σ)) (x, σ) :=
    ((D.hφ.differentiable (by simp)) (x, σ)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Vec d => ((x, σ) : Vec d × ℝ))
      (ContinuousLinearMap.inl ℝ (Vec d) ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const σ x)
  have h3 : fderiv ℝ (fun x : Vec d => D.φ (x, σ)) x =
      fderiv ℝ D.φ (x, σ) ∘L ContinuousLinearMap.inl ℝ (Vec d) ℝ := (h1.comp x h2).fderiv
  rw [h3]
  rfl

theorem contDiff_phi_slice (σ : ℝ) : ContDiff ℝ 1 fun x : Vec d => D.φ (x, σ) :=
  D.hφ.comp (contDiff_id.prodMk contDiff_const)

theorem fderiv_v_apply {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : σ ∈ Icc D.s D.t) {x : Vec d}
    (i : Fin d)
    (hDu : ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, σ) =
      ∫ y in D.K1, kern a (x - y) * D.Du (y, σ) i) :
    fderiv ℝ (fun x => D.v a (x, σ)) x (basisVec i) = mollT a D.K1 (fun z => D.Du z i) (x, σ) := by
  have h1 : fderiv ℝ (wholeSpaceMollify a (D.K1.indicator fun y => D.u (y, σ))) x (basisVec i) =
      ∫ y, fderiv ℝ (kern a) (x - y) (basisVec i) * (D.K1.indicator fun y => D.u (y, σ)) y :=
    moll_fderiv_apply ha ((D.slice_memLp hσ).locallyIntegrable (by norm_num)) x (basisVec i)
  have h2 : ∫ y, fderiv ℝ (kern a) (x - y) (basisVec i) *
      (D.K1.indicator fun y => D.u (y, σ)) y =
      ∫ y in D.K1, fderiv ℝ (kern a) (x - y) (basisVec i) * D.u (y, σ) := by
    rw [← integral_indicator D.K1_measurable]
    congr 1; funext y
    by_cases hy : y ∈ D.K1 <;> simp [hy]
  have h3 : mollT a D.K1 (fun z => D.Du z i) (x, σ) =
      ∫ y in D.K1, kern a (x - y) * D.Du (y, σ) i := by
    rw [mollT_eq, ← integral_indicator D.K1_measurable]
    congr 1; funext y
    by_cases hy : y ∈ D.K1 <;> simp [hy]
  change fderiv ℝ (wholeSpaceMollify a (D.K1.indicator fun y => D.u (y, σ))) x (basisVec i) = _
  rw [h1, h2, hDu, h3]


end SuperData

end PDE.Parabolic.Chain.Super
