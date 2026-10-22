module

public import EllipticRegularity.Parabolic.SliceEstimate.TimeEnergyCore

/-!
# `∂ₜ ∇u = ∇v` in the sense of distributions in time, tested with a fixed spatial weight

Abstract form: for the `EData` (every-time mollifications `Ab`, `Zb` absolutely continuous in time),
`∫ θ'(τ) ∫_K h W_i(·,τ) = - ∫ θ(τ) ∫_K h Z_i(·,τ)` for bounded measurable `h`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

namespace EData

variable (D : EData d)

theorem grad_time_joint {h : Vec d → ℝ} (hh : AEStronglyMeasurable h (volume.restrict D.K))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume.restrict D.K), |h x| ≤ C) (i : Fin d) {s t : ℝ}
    (hps : D.p ≤ s) (hst : s < t) (htq : t ≤ D.q) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hθs : tsupport θ ⊆ Ioo s t) :
    Integrable (fun z : Vec d × ℝ => (h z.1 * deriv θ z.2) * D.W i z)
        (volume.restrict (D.K ×ˢ Ioo s t)) ∧
      Integrable (fun z : Vec d × ℝ => (h z.1 * θ z.2) * D.Z i z)
        (volume.restrict (D.K ×ˢ Ioo s t)) ∧
      ∫ z, (h z.1 * deriv θ z.2) * D.W i z ∂(volume.restrict (D.K ×ˢ Ioo s t)) =
        -∫ z, (h z.1 * θ z.2) * D.Z i z ∂(volume.restrict (D.K ×ˢ Ioo s t)) := by
  set ν : Measure (Vec d × ℝ) := volume.restrict (D.K ×ˢ Ioo s t) with hνdef
  have hIoo : Ioo s t ⊆ Ioc D.p D.q := fun τ hτ => ⟨lt_of_le_of_lt hps hτ.1, hτ.2.le.trans htq⟩
  have hν : ν ≤ D.μ D.q := D.restrict_le hIoo
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top D.hK.measure_lt_top (by simp)
  have hν' : ν = (volume.restrict D.K).prod (volume.restrict (Ioo s t)) := volume_restrict_prod _ _
  -- weights
  have hθ'c : Continuous (deriv θ) := hθ.continuous_deriv le_rfl
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := s) (b := t)).exists_bound_of_continuousOn
    hθ'c.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := s) (b := t)).exists_bound_of_continuousOn
    hθ.continuous.continuousOn
  have hhfst : AEStronglyMeasurable (fun z : Vec d × ℝ => h z.1) ν := by
    rw [hν']
    exact hh.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict D.K) (ν := volume.restrict (Ioo s t)))
  have hCfst : ∀ᵐ z ∂ν, |h z.1| ≤ C := by
    rw [hν']
    exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict D.K)
      (ν := volume.restrict (Ioo s t))).ae hC
  have hzIoo : ∀ᵐ z ∂ν, z.2 ∈ Ioo s t :=
    (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioo)).2
      (Eventually.of_forall fun z hz => hz.2)
  set w1 : Vec d × ℝ → ℝ := fun z => h z.1 * deriv θ z.2 with hw1
  set w2 : Vec d × ℝ → ℝ := fun z => h z.1 * θ z.2 with hw2
  have hw1m : AEStronglyMeasurable w1 ν :=
    hhfst.mul ((hθ'c.comp continuous_snd).aestronglyMeasurable)
  have hw2m : AEStronglyMeasurable w2 ν :=
    hhfst.mul ((hθ.continuous.comp continuous_snd).aestronglyMeasurable)
  have hw1b : ∀ᵐ z ∂ν, |w1 z| ≤ C * M1 := by
    filter_upwards [hCfst, hzIoo] with z h1 h2
    have := hM1 z.2 ⟨h2.1.le, h2.2.le⟩
    rw [Real.norm_eq_abs] at this
    simp only [hw1, abs_mul]
    exact mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hw2b : ∀ᵐ z ∂ν, |w2 z| ≤ C * M2 := by
    filter_upwards [hCfst, hzIoo] with z h1 h2
    have := hM2 z.2 ⟨h2.1.le, h2.2.le⟩
    rw [Real.norm_eq_abs] at this
    simp only [hw2, abs_mul]
    exact mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hw1L : MemLp w1 2 ν := MemLp.of_bound hw1m (C * M1) hw1b
  have hw2L : MemLp w2 2 ν := MemLp.of_bound hw2m (C * M2) hw2b
  -- the identity at each scale
  have hAb := fun n i => (D.memLp_Ab le_rfl (D.aSeq_pos n) (D.aSeq_le_δ0 n) i)
  have hWZ := fun i => D.memLp_W le_rfl i
  have hper : ∀ n, ∫ z, w1 z * D.Ab i (D.aSeq n) z.1 z.2 ∂ν =
      -∫ z, w2 z * D.Zb i (D.aSeq n) z.1 z.2 ∂ν := by
    intro n
    have ha := D.aSeq_pos n
    have haδ := D.aSeq_le_δ0 n
    have i1 : Integrable (fun z => w1 z * D.Ab i (D.aSeq n) z.1 z.2) ν := by
      have := (((hAb n i).1.mono_measure hν).integrable one_le_two).bdd_mul hw1m (c := C * M1)
        (hw1b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
      exact this
    have i2 : Integrable (fun z => w2 z * D.Zb i (D.aSeq n) z.1 z.2) ν := by
      have := (((hAb n i).2.mono_measure hν).integrable one_le_two).bdd_mul hw2m (c := C * M2)
        (hw2b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
      exact this
    have hy : ∀ y ∈ D.K, ∫ τ in Ioo s t, deriv θ τ * D.Ab i (D.aSeq n) y τ =
        -∫ τ in Ioo s t, θ τ * D.Zb i (D.aSeq n) y τ := by
      intro y hy
      refine ibp_ac hps hst htq (D.hZint _ ha haδ y hy i) (fun τ hτ => ?_) hθ hθs
      have := D.hAC _ ha haδ y hy i D.p τ le_rfl hτ.1 hτ.2
      linarith
    rw [hν'] at i1 i2 ⊢
    rw [integral_prod _ i1, integral_prod _ i2, ← integral_neg]
    refine setIntegral_congr_fun D.K_measurable fun y hy' => ?_
    simp only [hw1, hw2]
    have e1 : ∫ τ in Ioo s t, h y * deriv θ τ * D.Ab i (D.aSeq n) y τ =
        h y * ∫ τ in Ioo s t, deriv θ τ * D.Ab i (D.aSeq n) y τ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    have e2 : ∫ τ in Ioo s t, h y * θ τ * D.Zb i (D.aSeq n) y τ =
        h y * ∫ τ in Ioo s t, θ τ * D.Zb i (D.aSeq n) y τ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    rw [e1, e2, hy y hy']
    ring
  -- the limits
  have hL1 : ∀ n, MemLp (fun z : Vec d × ℝ => D.Ab i (D.aSeq n) z.1 z.2) 2 ν := fun n =>
    (hAb n i).1.mono_measure hν
  have hL2 : ∀ n, MemLp (fun z : Vec d × ℝ => D.Zb i (D.aSeq n) z.1 z.2) 2 ν := fun n =>
    (hAb n i).2.mono_measure hν
  have hl1 : Tendsto (fun n => eLpNorm ((fun z : Vec d × ℝ => D.Ab i (D.aSeq n) z.1 z.2) - D.W i)
      2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (D.tendsto_Ab i).1
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hν)
  have hl2 : Tendsto (fun n => eLpNorm ((fun z : Vec d × ℝ => D.Zb i (D.aSeq n) z.1 z.2) - D.Z i)
      2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (D.tendsto_Ab i).2
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hν)
  have hg0 : ∀ g : Vec d × ℝ → ℝ, Tendsto (fun _ : ℕ => eLpNorm (g - g) 2 ν) atTop (𝓝 0) := fun g => by
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  have t1 := tendsto_integral_mul_of_L2 (μ := ν) (F := fun n z => D.Ab i (D.aSeq n) z.1 z.2)
    (G := fun _ => w1) (F0 := D.W i) (G0 := w1) hL1 (fun _ => hw1L) ((hWZ i).1.mono_measure hν)
    hw1L hl1 (hg0 w1)
  have t2 := tendsto_integral_mul_of_L2 (μ := ν) (F := fun n z => D.Zb i (D.aSeq n) z.1 z.2)
    (G := fun _ => w2) (F0 := D.Z i) (G0 := w2) hL2 (fun _ => hw2L) ((hWZ i).2.mono_measure hν)
    hw2L hl2 (hg0 w2)
  have hcomm : ∀ (f g : Vec d × ℝ → ℝ), (fun z => f z * g z) = fun z => g z * f z := fun f g => by
    funext z; ring
  simp only [mul_comm] at t1 t2
  have hlim : ∫ z, w1 z * D.W i z ∂ν = -∫ z, w2 z * D.Z i z ∂ν := by
    refine tendsto_nhds_unique (t1.congr hper) ?_
    exact t2.neg
  have j1 : Integrable (fun z => w1 z * D.W i z) ν :=
    (((hWZ i).1.mono_measure hν).integrable one_le_two).bdd_mul hw1m (c := C * M1)
      (hw1b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  have j2 : Integrable (fun z => w2 z * D.Z i z) ν :=
    (((hWZ i).2.mono_measure hν).integrable one_le_two).bdd_mul hw2m (c := C * M2)
      (hw2b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  exact ⟨j1, j2, hlim⟩

theorem grad_time_identity {h : Vec d → ℝ} (hh : AEStronglyMeasurable h (volume.restrict D.K))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume.restrict D.K), |h x| ≤ C) (i : Fin d) {s t : ℝ}
    (hps : D.p ≤ s) (hst : s < t) (htq : t ≤ D.q) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hθs : tsupport θ ⊆ Ioo s t) :
    ∫ τ in Ioo s t, deriv θ τ * ∫ y in D.K, h y * D.W i (y, τ) =
      -∫ τ in Ioo s t, θ τ * ∫ y in D.K, h y * D.Z i (y, τ) := by
  set ν : Measure (Vec d × ℝ) := volume.restrict (D.K ×ˢ Ioo s t) with hνdef
  have hIoo : Ioo s t ⊆ Ioc D.p D.q := fun τ hτ => ⟨lt_of_le_of_lt hps hτ.1, hτ.2.le.trans htq⟩
  have hν : ν ≤ D.μ D.q := D.restrict_le hIoo
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top D.hK.measure_lt_top (by simp)
  have hν' : ν = (volume.restrict D.K).prod (volume.restrict (Ioo s t)) := volume_restrict_prod _ _
  -- weights
  have hθ'c : Continuous (deriv θ) := hθ.continuous_deriv le_rfl
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := s) (b := t)).exists_bound_of_continuousOn
    hθ'c.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := s) (b := t)).exists_bound_of_continuousOn
    hθ.continuous.continuousOn
  have hhfst : AEStronglyMeasurable (fun z : Vec d × ℝ => h z.1) ν := by
    rw [hν']
    exact hh.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict D.K) (ν := volume.restrict (Ioo s t)))
  have hCfst : ∀ᵐ z ∂ν, |h z.1| ≤ C := by
    rw [hν']
    exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict D.K)
      (ν := volume.restrict (Ioo s t))).ae hC
  have hzIoo : ∀ᵐ z ∂ν, z.2 ∈ Ioo s t :=
    (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioo)).2
      (Eventually.of_forall fun z hz => hz.2)
  set w1 : Vec d × ℝ → ℝ := fun z => h z.1 * deriv θ z.2 with hw1
  set w2 : Vec d × ℝ → ℝ := fun z => h z.1 * θ z.2 with hw2
  have hw1m : AEStronglyMeasurable w1 ν :=
    hhfst.mul ((hθ'c.comp continuous_snd).aestronglyMeasurable)
  have hw2m : AEStronglyMeasurable w2 ν :=
    hhfst.mul ((hθ.continuous.comp continuous_snd).aestronglyMeasurable)
  have hw1b : ∀ᵐ z ∂ν, |w1 z| ≤ C * M1 := by
    filter_upwards [hCfst, hzIoo] with z h1 h2
    have := hM1 z.2 ⟨h2.1.le, h2.2.le⟩
    rw [Real.norm_eq_abs] at this
    simp only [hw1, abs_mul]
    exact mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hw2b : ∀ᵐ z ∂ν, |w2 z| ≤ C * M2 := by
    filter_upwards [hCfst, hzIoo] with z h1 h2
    have := hM2 z.2 ⟨h2.1.le, h2.2.le⟩
    rw [Real.norm_eq_abs] at this
    simp only [hw2, abs_mul]
    exact mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hw1L : MemLp w1 2 ν := MemLp.of_bound hw1m (C * M1) hw1b
  have hw2L : MemLp w2 2 ν := MemLp.of_bound hw2m (C * M2) hw2b
  -- the identity at each scale
  have hAb := fun n i => (D.memLp_Ab le_rfl (D.aSeq_pos n) (D.aSeq_le_δ0 n) i)
  have hWZ := fun i => D.memLp_W le_rfl i
  have hper : ∀ n, ∫ z, w1 z * D.Ab i (D.aSeq n) z.1 z.2 ∂ν =
      -∫ z, w2 z * D.Zb i (D.aSeq n) z.1 z.2 ∂ν := by
    intro n
    have ha := D.aSeq_pos n
    have haδ := D.aSeq_le_δ0 n
    have i1 : Integrable (fun z => w1 z * D.Ab i (D.aSeq n) z.1 z.2) ν := by
      have := (((hAb n i).1.mono_measure hν).integrable one_le_two).bdd_mul hw1m (c := C * M1)
        (hw1b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
      exact this
    have i2 : Integrable (fun z => w2 z * D.Zb i (D.aSeq n) z.1 z.2) ν := by
      have := (((hAb n i).2.mono_measure hν).integrable one_le_two).bdd_mul hw2m (c := C * M2)
        (hw2b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
      exact this
    have hy : ∀ y ∈ D.K, ∫ τ in Ioo s t, deriv θ τ * D.Ab i (D.aSeq n) y τ =
        -∫ τ in Ioo s t, θ τ * D.Zb i (D.aSeq n) y τ := by
      intro y hy
      refine ibp_ac hps hst htq (D.hZint _ ha haδ y hy i) (fun τ hτ => ?_) hθ hθs
      have := D.hAC _ ha haδ y hy i D.p τ le_rfl hτ.1 hτ.2
      linarith
    rw [hν'] at i1 i2 ⊢
    rw [integral_prod _ i1, integral_prod _ i2, ← integral_neg]
    refine setIntegral_congr_fun D.K_measurable fun y hy' => ?_
    simp only [hw1, hw2]
    have e1 : ∫ τ in Ioo s t, h y * deriv θ τ * D.Ab i (D.aSeq n) y τ =
        h y * ∫ τ in Ioo s t, deriv θ τ * D.Ab i (D.aSeq n) y τ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    have e2 : ∫ τ in Ioo s t, h y * θ τ * D.Zb i (D.aSeq n) y τ =
        h y * ∫ τ in Ioo s t, θ τ * D.Zb i (D.aSeq n) y τ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    rw [e1, e2, hy y hy']
    ring
  -- the limits
  have hL1 : ∀ n, MemLp (fun z : Vec d × ℝ => D.Ab i (D.aSeq n) z.1 z.2) 2 ν := fun n =>
    (hAb n i).1.mono_measure hν
  have hL2 : ∀ n, MemLp (fun z : Vec d × ℝ => D.Zb i (D.aSeq n) z.1 z.2) 2 ν := fun n =>
    (hAb n i).2.mono_measure hν
  have hl1 : Tendsto (fun n => eLpNorm ((fun z : Vec d × ℝ => D.Ab i (D.aSeq n) z.1 z.2) - D.W i)
      2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (D.tendsto_Ab i).1
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hν)
  have hl2 : Tendsto (fun n => eLpNorm ((fun z : Vec d × ℝ => D.Zb i (D.aSeq n) z.1 z.2) - D.Z i)
      2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (D.tendsto_Ab i).2
      (fun n => bot_le) (fun n => eLpNorm_mono_measure _ hν)
  have hg0 : ∀ g : Vec d × ℝ → ℝ, Tendsto (fun _ : ℕ => eLpNorm (g - g) 2 ν) atTop (𝓝 0) := fun g => by
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  have t1 := tendsto_integral_mul_of_L2 (μ := ν) (F := fun n z => D.Ab i (D.aSeq n) z.1 z.2)
    (G := fun _ => w1) (F0 := D.W i) (G0 := w1) hL1 (fun _ => hw1L) ((hWZ i).1.mono_measure hν)
    hw1L hl1 (hg0 w1)
  have t2 := tendsto_integral_mul_of_L2 (μ := ν) (F := fun n z => D.Zb i (D.aSeq n) z.1 z.2)
    (G := fun _ => w2) (F0 := D.Z i) (G0 := w2) hL2 (fun _ => hw2L) ((hWZ i).2.mono_measure hν)
    hw2L hl2 (hg0 w2)
  have hcomm : ∀ (f g : Vec d × ℝ → ℝ), (fun z => f z * g z) = fun z => g z * f z := fun f g => by
    funext z; ring
  simp only [mul_comm] at t1 t2
  have hlim : ∫ z, w1 z * D.W i z ∂ν = -∫ z, w2 z * D.Z i z ∂ν := by
    refine tendsto_nhds_unique (t1.congr hper) ?_
    exact t2.neg
  -- Fubini on the limit
  have j1 : Integrable (fun z => w1 z * D.W i z) ν :=
    (((hWZ i).1.mono_measure hν).integrable one_le_two).bdd_mul hw1m (c := C * M1)
      (hw1b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  have j2 : Integrable (fun z => w2 z * D.Z i z) ν :=
    (((hWZ i).2.mono_measure hν).integrable one_le_two).bdd_mul hw2m (c := C * M2)
      (hw2b.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  rw [hν'] at j1 j2 hlim
  rw [integral_prod_symm _ j1, integral_prod_symm _ j2] at hlim
  have e1 : ∀ τ, ∫ y in D.K, w1 (y, τ) * D.W i (y, τ) =
      deriv θ τ * ∫ y in D.K, h y * D.W i (y, τ) := by
    intro τ
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hw1]; ring
  have e2 : ∀ τ, ∫ y in D.K, w2 (y, τ) * D.Z i (y, τ) =
      θ τ * ∫ y in D.K, h y * D.Z i (y, τ) := by
    intro τ
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hw2]; ring
  simp only [e1, e2] at hlim
  exact hlim

end EData

end PDE.Parabolic.Slice
