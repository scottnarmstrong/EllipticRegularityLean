module

public import PDEFoundation.Euler.L2Limit
public import PDEFoundation.Euler.MollifyL2ST

/-!
# A space-time `L²` limit from slice convergence (part 1): Cauchy criterion and slice square norms
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PDE

theorem exists_tendsto_eLpNorm_two_of_cauchy {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → α → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (hc : Tendsto (fun n : ℕ × ℕ => eLpNorm (f n.1 - f n.2) 2 μ) atTop (𝓝 0)) :
    ∃ g : α → E, MemLp g 2 μ ∧ Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hc' : CauchySeq (fun n => (hf n).toLp (f n)) := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le)
      (fun n => ?_)
    refine le_of_eq ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hf n.1).coeFn_toLp, (hf n.2).coeFn_toLp] with x h2 h3
    simp only [Pi.sub_apply, h2, h3]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc'
  refine ⟨L, Lp.memLp L, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ L).1 hL
  refine this.congr (fun n => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hf n).coeFn_toLp] with x h2
  simp only [Pi.sub_apply, h2]

end PDE

namespace PDE

section Slices

variable {T : ℝ}

theorem lintegral_slice_sq {g : Vec 2 → ℝ} (hg : AEStronglyMeasurable g (volume.restrict torusCube)) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(volume.restrict torusCube) = eLpNorm g 2 (volume.restrict torusCube) ^ 2 :=
  lintegral_enorm_sq_eq _ g hg

theorem lintegral_spacetime_sq {h : Vec 2 × ℝ → ℝ} (hm : Measurable h) :
    eLpNorm h 2 (eulerMeasure T) ^ 2 =
      ∫⁻ t, ∫⁻ x, ‖h (x, t)‖ₑ ^ 2 ∂(volume.restrict torusCube) ∂(volume.restrict (Icc (0 : ℝ) T)) := by
  rw [← lintegral_enorm_sq_eq _ h hm.aestronglyMeasurable, eulerMeasure_eq_prod]
  exact lintegral_prod_symm' (fun z => ‖h z‖ₑ ^ 2) (hm.enorm.pow_const 2)

theorem spacetime_cauchy_of_slices {f : ℕ → Vec 2 × ℝ → ℝ} {C : ℝ} (hf : ∀ k, Measurable (f k))
    (hbd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ k,
      eLpNorm (fun x => f k (x, t)) 2 (volume.restrict torusCube) ≤ ENNReal.ofReal C)
    (hsl : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ g : Vec 2 → ℝ,
      MemLp g 2 (volume.restrict torusCube) ∧
      Tendsto (fun k => eLpNorm (fun x => f k (x, t) - g x) 2 (volume.restrict torusCube)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 (eulerMeasure T)) atTop (𝓝 0) := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set sl : ℕ × ℕ → ℝ → ℝ≥0∞ := fun p t => ∫⁻ x, ‖f p.1 (x, t) - f p.2 (x, t)‖ₑ ^ 2 ∂μc with hsl_def
  have hsm : ∀ p, Measurable (sl p) := fun p => by
    have : Measurable (fun z : Vec 2 × ℝ => ‖f p.1 z - f p.2 z‖ₑ ^ 2) :=
      (((hf p.1).sub (hf p.2)).enorm).pow_const 2
    exact this.lintegral_prod_left'
  have hslm : ∀ k t, AEStronglyMeasurable (fun x => f k (x, t)) μc := fun k t =>
    ((hf k).comp measurable_prodMk_right).aestronglyMeasurable
  have hbound : ∀ p, ∀ᵐ t ∂ν, sl p t ≤ (2 * ENNReal.ofReal C) ^ 2 := by
    intro p
    filter_upwards [hbd] with t ht
    have e : sl p t = eLpNorm (fun x => f p.1 (x, t) - f p.2 (x, t)) 2 μc ^ 2 :=
      lintegral_slice_sq ((hslm p.1 t).sub (hslm p.2 t))
    rw [e]
    gcongr
    calc eLpNorm (fun x => f p.1 (x, t) - f p.2 (x, t)) 2 μc
        ≤ eLpNorm (fun x => f p.1 (x, t)) 2 μc + eLpNorm (fun x => f p.2 (x, t)) 2 μc :=
          eLpNorm_sub_le (f := fun x => f p.1 (x, t)) (g := fun x => f p.2 (x, t)) (by norm_num)
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (ht _) (ht _)
      _ = 2 * ENNReal.ofReal C := by rw [two_mul]
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun p : ℕ × ℕ => sl p t) atTop (𝓝 0) := by
    filter_upwards [hsl] with t ⟨g, hg, hgt⟩
    have hprod : (atTop : Filter (ℕ × ℕ)) = atTop ×ˢ atTop := Filter.prod_atTop_atTop_eq.symm
    have h1 : Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x => f p.1 (x, t) - g x) 2 μc) atTop (𝓝 0) := by
      rw [hprod]; exact hgt.comp tendsto_fst
    have h2 : Tendsto (fun p : ℕ × ℕ => eLpNorm (fun x => f p.2 (x, t) - g x) 2 μc) atTop (𝓝 0) := by
      rw [hprod]; exact hgt.comp tendsto_snd
    have h3 : Tendsto (fun p : ℕ × ℕ => (eLpNorm (fun x => f p.1 (x, t) - g x) 2 μc +
        eLpNorm (fun x => f p.2 (x, t) - g x) 2 μc) ^ 2) atTop (𝓝 0) := by
      have h12 := h1.add h2
      rw [add_zero] at h12
      have := ((ENNReal.continuous_pow 2).tendsto 0).comp h12
      simpa [Function.comp_def] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) (fun p => ?_)
    have e : sl p t = eLpNorm (fun x => f p.1 (x, t) - f p.2 (x, t)) 2 μc ^ 2 :=
      lintegral_slice_sq ((hslm p.1 t).sub (hslm p.2 t))
    rw [e]
    gcongr
    calc eLpNorm (fun x => f p.1 (x, t) - f p.2 (x, t)) 2 μc
        = eLpNorm ((fun x => f p.1 (x, t) - g x) - (fun x => f p.2 (x, t) - g x)) 2 μc := by
          congr 1; funext x; simp
      _ ≤ _ := eLpNorm_sub_le (by norm_num)
  have hdct := tendsto_lintegral_filter_of_dominated_convergence (μ := ν) (l := (atTop : Filter (ℕ × ℕ)))
    (F := sl) (f := fun _ => 0) (fun _ => (2 * ENNReal.ofReal C) ^ 2)
    (Eventually.of_forall hsm) (Eventually.of_forall hbound) (by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
        (measure_ne_top _ _)) hlim
  simp only [lintegral_zero] at hdct
  have hsq : ∀ p : ℕ × ℕ, eLpNorm (f p.1 - f p.2) 2 (eulerMeasure T) ^ 2 = ∫⁻ t, sl p t ∂ν := fun p =>
    lintegral_spacetime_sq ((hf p.1).sub (hf p.2))
  have hsq' : Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 (eulerMeasure T) ^ 2) atTop (𝓝 0) :=
    hdct.congr (fun p => (hsq p).symm)
  have hroot := ((ENNReal.continuous_rpow_const (y := (2⁻¹ : ℝ))).tendsto 0).comp hsq'
  have e0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [e0] at hroot
  refine hroot.congr (fun p => ?_)
  simp only [Function.comp]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end Slices

end PDE
