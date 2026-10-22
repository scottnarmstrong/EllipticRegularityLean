module

public import PDEFoundation.Euler.SpaceTimeCauchy

/-!
# A space-time `L²` limit from slice convergence (part 2)

If measurable `fₖ` on `cube × [0,T]` have slice `L²(cube)`-norms bounded by `C` for a.e. `t` and, for a.e. `t`,
`fₖ(·,t)` converges in `L²(cube)` (to some limit that is not assumed measurable in `t`), then `fₖ` converges in
`L²(cube × [0,T])` to a jointly measurable `F`, and for a.e. `t` the whole sequence `fₖ(·,t)` converges to `F(·,t)` in
`L²(cube)`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PDE

section

variable {T : ℝ}

theorem memLp_spacetime_of_slices {h : Vec 2 × ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hbd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      eLpNorm (fun x => h (x, t)) 2 (volume.restrict torusCube) ≤ ENNReal.ofReal C) :
    MemLp h 2 (eulerMeasure T) := by
  have hsq := lintegral_spacetime_sq (T := T) hm
  have hle : eLpNorm h 2 (eulerMeasure T) ^ 2 ≤ ∫⁻ _t, ENNReal.ofReal C ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T)) := by
    rw [hsq]
    refine lintegral_mono_ae ?_
    filter_upwards [hbd] with t ht
    have e := lintegral_slice_sq (g := fun x => h (x, t))
      ((hm.comp (measurable_prodMk_right (y := t))).aestronglyMeasurable)
    rw [e]
    gcongr
  rw [lintegral_const] at hle
  have hfin : ENNReal.ofReal C ^ 2 * (volume.restrict (Icc (0 : ℝ) T)) univ < ∞ := by
    refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ?_
    rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top
  by_contra hne
  have hne' : eLpNorm h 2 (eulerMeasure T) = ⊤ := by
    by_contra h2
    exact hne (lt_top_iff_ne_top.2 h2)
  rw [hne'] at hle
  simp only [ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0), top_le_iff] at hle
  rw [hle] at hfin
  exact absurd hfin (by simp)

theorem slice_measurable {h : Vec 2 × ℝ → ℝ} (hm : Measurable h) (t : ℝ) :
    AEStronglyMeasurable (fun x => h (x, t)) (volume.restrict torusCube) :=
  (hm.comp (measurable_prodMk_right (y := t))).aestronglyMeasurable

theorem ae_subseq_slice_conv {f : ℕ → Vec 2 × ℝ → ℝ} {F : Vec 2 × ℝ → ℝ}
    (hf : ∀ k, Measurable (f k)) (hF : Measurable F)
    (hfin : ∀ k, MemLp (f k - F) 2 (eulerMeasure T))
    (hconv : Tendsto (fun k => eLpNorm (f k - F) 2 (eulerMeasure T)) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun i => eLpNorm (fun x => f (ns i) (x, t) - F (x, t)) 2 (volume.restrict torusCube))
        atTop (𝓝 0) := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  set φ : ℕ → ℝ → ℝ≥0∞ := fun k t => ∫⁻ x, ‖f k (x, t) - F (x, t)‖ₑ ^ 2 ∂μc with hφ
  have hφm : ∀ k, Measurable (φ k) := fun k => by
    have : Measurable (fun z : Vec 2 × ℝ => ‖f k z - F z‖ₑ ^ 2) :=
      (((hf k).sub hF).enorm).pow_const 2
    exact this.lintegral_prod_left'
  have hφint : ∀ k, ∫⁻ t, φ k t ∂ν = eLpNorm (f k - F) 2 (eulerMeasure T) ^ 2 := fun k => by
    have := lintegral_spacetime_sq (T := T) ((hf k).sub hF)
    rw [this]
    rfl
  have hφfin : ∀ᵐ t ∂ν, ∀ k, φ k t < ∞ := by
    rw [ae_all_iff]
    intro k
    refine ae_lt_top (hφm k) ?_
    rw [hφint k]
    exact ENNReal.pow_ne_top (hfin k).ne
  set ψ : ℕ → ℝ → ℝ := fun k t => (φ k t).toReal with hψ
  have hψ1 : Tendsto (fun k => eLpNorm (ψ k - 0) 1 ν) atTop (𝓝 0) := by
    have hsq : Tendsto (fun k => eLpNorm (f k - F) 2 (eulerMeasure T) ^ 2) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_pow 2).tendsto 0).comp hconv
      simpa [Function.comp_def] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq (fun _ => bot_le)
      (fun k => ?_)
    rw [← hφint k, eLpNorm_one_eq_lintegral_enorm]
    · refine lintegral_mono fun t => ?_
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, hψ, Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    · exact (hφm k).ennreal_toReal.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hψ1
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hφfin] with t ht hfin'
  have h0 : Tendsto (fun i => φ (ns i) t) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal_iff (fun i => (hfin' (ns i)).ne) ENNReal.zero_ne_top).1
      (by simpa [hψ] using ht)
    exact this
  have hsl : ∀ i, φ (ns i) t = eLpNorm (fun x => f (ns i) (x, t) - F (x, t)) 2 μc ^ 2 := fun i =>
    lintegral_slice_sq (slice_measurable ((hf (ns i)).sub hF) t)
  have hsq : Tendsto (fun i => eLpNorm (fun x => f (ns i) (x, t) - F (x, t)) 2 μc ^ 2) atTop (𝓝 0) :=
    h0.congr hsl
  have hroot := ((ENNReal.continuous_rpow_const (y := (2⁻¹ : ℝ))).tendsto 0).comp hsq
  have e0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [e0] at hroot
  refine hroot.congr (fun i => ?_)
  simp only [Function.comp]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem exists_spacetime_limit_meas {f : ℕ → Vec 2 × ℝ → ℝ} {C : ℝ} (hf : ∀ k, Measurable (f k))
    (hbd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ k,
      eLpNorm (fun x => f k (x, t)) 2 (volume.restrict torusCube) ≤ ENNReal.ofReal C)
    (hsl : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ g : Vec 2 → ℝ,
      MemLp g 2 (volume.restrict torusCube) ∧
      Tendsto (fun k => eLpNorm (fun x => f k (x, t) - g x) 2 (volume.restrict torusCube)) atTop (𝓝 0)) :
    ∃ F : Vec 2 × ℝ → ℝ, Measurable F ∧ MemLp F 2 (eulerMeasure T) ∧
      Tendsto (fun k => eLpNorm (f k - F) 2 (eulerMeasure T)) atTop (𝓝 0) ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        Tendsto (fun k => eLpNorm (fun x => f k (x, t) - F (x, t)) 2 (volume.restrict torusCube))
          atTop (𝓝 0) := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  have hmem : ∀ k, MemLp (f k) 2 (eulerMeasure T) := fun k =>
    memLp_spacetime_of_slices (hf k) (hbd.mono fun t ht => ht k)
  have hcau := spacetime_cauchy_of_slices hf hbd hsl
  obtain ⟨F0, hF0, hconv0⟩ := exists_tendsto_eLpNorm_two_of_cauchy hmem hcau
  set F : Vec 2 × ℝ → ℝ := hF0.aestronglyMeasurable.mk F0 with hFdef
  have hFm : Measurable F := hF0.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFae : F0 =ᵐ[eulerMeasure T] F := hF0.aestronglyMeasurable.ae_eq_mk
  have hFmem : MemLp F 2 (eulerMeasure T) := hF0.ae_eq hFae
  have hconv : Tendsto (fun k => eLpNorm (f k - F) 2 (eulerMeasure T)) atTop (𝓝 0) := by
    refine hconv0.congr (fun k => eLpNorm_congr_ae ?_)
    filter_upwards [hFae] with z hz
    simp [hz]
  have hfin : ∀ k, MemLp (f k - F) 2 (eulerMeasure T) := fun k => (hmem k).sub hFmem
  obtain ⟨ns, hns, hsub⟩ := ae_subseq_slice_conv hf hFm hfin hconv
  refine ⟨F, hFm, hFmem, hconv, ?_⟩
  filter_upwards [hsub, hsl] with t h1 ⟨g, hg, hgt⟩
  have hFt_meas : AEStronglyMeasurable (fun x => F (x, t)) μc := slice_measurable hFm t
  have hup : Tendsto (fun i => eLpNorm (fun x => f (ns i) (x, t) - F (x, t)) 2 μc +
      eLpNorm (fun x => f (ns i) (x, t) - g x) 2 μc) atTop (𝓝 0) := by
    have := h1.add (hgt.comp hns.tendsto_atTop)
    simpa using this
  have hle : ∀ i, eLpNorm (fun x => F (x, t) - g x) 2 μc ≤ eLpNorm (fun x => f (ns i) (x, t) - F (x, t)) 2 μc +
      eLpNorm (fun x => f (ns i) (x, t) - g x) 2 μc := by
    intro i
    calc eLpNorm (fun x => F (x, t) - g x) 2 μc
        = eLpNorm ((fun x => f (ns i) (x, t) - g x) - (fun x => f (ns i) (x, t) - F (x, t))) 2 μc := by
          congr 1; funext x; simp
      _ ≤ eLpNorm (fun x => f (ns i) (x, t) - g x) 2 μc +
          eLpNorm (fun x => f (ns i) (x, t) - F (x, t)) 2 μc := eLpNorm_sub_le (by norm_num)
      _ = _ := add_comm _ _
  have hzero : eLpNorm (fun x => F (x, t) - g x) 2 μc = 0 := by
    have := ge_of_tendsto' hup hle
    exact le_antisymm this bot_le
  have hae : (fun x => F (x, t)) =ᵐ[μc] g := by
    have := (eLpNorm_eq_zero_iff (by norm_num)).1 hzero
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx
  refine hgt.congr (fun k => eLpNorm_congr_ae ?_)
  filter_upwards [hae] with x hx
  simp [hx]

theorem exists_spacetime_limit {f : ℕ → Vec 2 × ℝ → ℝ} {C : ℝ}
    (hf : ∀ k, AEStronglyMeasurable (f k) (eulerMeasure T))
    (hbd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ k,
      eLpNorm (fun x => f k (x, t)) 2 (volume.restrict torusCube) ≤ ENNReal.ofReal C)
    (hsl : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ g : Vec 2 → ℝ,
      MemLp g 2 (volume.restrict torusCube) ∧
      Tendsto (fun k => eLpNorm (fun x => f k (x, t) - g x) 2 (volume.restrict torusCube)) atTop (𝓝 0)) :
    ∃ F : Vec 2 × ℝ → ℝ, Measurable F ∧ MemLp F 2 (eulerMeasure T) ∧
      Tendsto (fun k => eLpNorm (f k - F) 2 (eulerMeasure T)) atTop (𝓝 0) ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        Tendsto (fun k => eLpNorm (fun x => f k (x, t) - F (x, t)) 2 (volume.restrict torusCube))
          atTop (𝓝 0) := by
  set f' : ℕ → Vec 2 × ℝ → ℝ := fun k => (hf k).mk (f k) with hf'
  have hf'm : ∀ k, Measurable (f' k) := fun k => (hf k).stronglyMeasurable_mk.measurable
  have hae : ∀ k, f k =ᵐ[eulerMeasure T] f' k := fun k => (hf k).ae_eq_mk
  have hk : ∀ k, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      (fun x => f k (x, t)) =ᵐ[volume.restrict torusCube] (fun x => f' k (x, t)) := fun k => by
    have h1 := hae k
    rw [eulerMeasure_eq_prod] at h1
    have h2 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
      (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae h1
    exact Measure.ae_ae_of_ae_prod h2
  have hsliceae := ae_all_iff.2 hk
  have hbd' : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ k,
      eLpNorm (fun x => f' k (x, t)) 2 (volume.restrict torusCube) ≤ ENNReal.ofReal C := by
    filter_upwards [hbd, hsliceae] with t ht hs k
    rw [← eLpNorm_congr_ae (hs k)]
    exact ht k
  have hsl' : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ g : Vec 2 → ℝ,
      MemLp g 2 (volume.restrict torusCube) ∧
      Tendsto (fun k => eLpNorm (fun x => f' k (x, t) - g x) 2 (volume.restrict torusCube)) atTop (𝓝 0) := by
    filter_upwards [hsl, hsliceae] with t ⟨g, hg, hgt⟩ hs
    refine ⟨g, hg, hgt.congr (fun k => eLpNorm_congr_ae ?_)⟩
    filter_upwards [hs k] with x hx
    simp [hx]
  obtain ⟨F, hFm, hFmem, hconv, hslice⟩ := exists_spacetime_limit_meas hf'm hbd' hsl'
  refine ⟨F, hFm, hFmem, ?_, ?_⟩
  · refine hconv.congr (fun k => eLpNorm_congr_ae ?_)
    filter_upwards [hae k] with z hz
    simp [hz]
  · filter_upwards [hslice, hsliceae] with t ht hs
    refine ht.congr (fun k => eLpNorm_congr_ae ?_)
    filter_upwards [hs k] with x hx
    simp [hx]

end

end PDE
