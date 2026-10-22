module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.SmoothLayer

/-!
# Smooth case: the limit `h → 0` (conditional on Brunn--Minkowski)

Combining the layer-cake erosion estimate with `ν_h(s) ≥ μ(s + ω_f(h))` and letting `h → 0⁺`
gives `d |B_1|^{1/d} ∫_0^∞ μ(s)^{(d-1)/d} ds ≤ ∫ |∇ψ|` for `ψ ∈ C^1_c`, `d ≥ 2`, where
`μ(s) = |{|ψ| ≥ s}|`. The Brunn--Minkowski inequality is an explicit hypothesis.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Pointwise ENNReal

namespace PDE.SobolevSharp

variable {d : ℕ}

theorem lintegral_Ioi_comp_add (F : ℝ → ℝ≥0∞) (ω : ℝ) :
    ∫⁻ s in Ioi (0 : ℝ), F (s + ω) = ∫⁻ s in Ioi ω, F s := by
  have h1 : ∀ s : ℝ, (Ioi ω).indicator F (s + ω) = (Ioi (0 : ℝ)).indicator (fun s => F (s + ω)) s := by
    intro s
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s + ω ∈ Ioi ω from by simpa using hs),
        indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    · rw [indicator_of_notMem (show s + ω ∉ Ioi ω from by simpa using hs),
        indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_right_eq_self ((Ioi ω).indicator F) ω]
  exact lintegral_congr fun s => (h1 s).symm

section Limit

variable {ψ : Vec d → ℝ}

/-- For every `ω₀ > 0`, the tail integral is bounded by the `L¹` norm of the gradient. -/
theorem sharp_tail_bound (hd : 2 ≤ d)
    (BM : ∀ A B : Set (Vec d), IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
      volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d))
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) {ω₀ : ℝ} (hω₀ : 0 < ω₀) :
    ∫⁻ s in Ioi ω₀, sharpConst d * volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) ≤
      ENNReal.ofReal (∫ x, gradNorm ψ x) := by
  have hf := continuous_abs_comp hψ.continuous
  have hfc := hasCompactSupport_abs_comp hc
  have hgc := continuous_gradNorm hψ
  have hgcs := hasCompactSupport_gradNorm hc
  have he : 0 ≤ ((d : ℝ) - 1) / d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    exact div_nonneg (by linarith) (by linarith)
  set K1 := (volume (supportNbhd ψ 1)).toReal with hK1
  set T := ∫⁻ s in Ioi ω₀, sharpConst d * volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) with hT
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), T ≤ ENNReal.ofReal ((∫ x, gradNorm ψ x) +
      modulus (gradNorm ψ) h * K1) := by
    have e1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
    have e2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), modulus (fun y => |ψ y|) h ≤ ω₀ :=
      (tendsto_modulus hf hfc).eventually (ge_mem_nhds hω₀)
    filter_upwards [e1, e2] with h hh1 hh2
    have hω := modulus_nonneg hgc hgcs hh1.1.le
    have hωf := modulus_nonneg hf hfc hh1.1.le
    have hstep := sharp_step_integrated hd BM hψ hc hh1.1
    have hmono : ∫⁻ s in Ioi (0 : ℝ), sharpConst d *
        volume {x | s + modulus (fun y => |ψ y|) h ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) ≤
        ∫⁻ s in Ioi (0 : ℝ), sharpConst d *
          volume (erosionSet (fun y => |ψ y|) h s) ^ (((d : ℝ) - 1) / d) := by
      refine lintegral_mono fun s => ?_
      exact mul_le_mul_right (ENNReal.rpow_le_rpow
        (measure_mono (superlevel_modulus_subset_erosionSet hf hfc hh1.1.le s)) he) _
    have hK : (volume (supportNbhd ψ h)).toReal ≤ K1 := by
      refine ENNReal.toReal_mono (measure_supportNbhd_lt_top hc zero_le_one).ne
        (measure_mono ?_)
      exact add_subset_add_left (euclideanClosedBall_mono hh1.1.le hh1.2)
    calc T ≤ ∫⁻ s in Ioi (modulus (fun y => |ψ y|) h), sharpConst d *
            volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) :=
          lintegral_mono_set (Ioi_subset_Ioi hh2)
      _ = _ := (lintegral_Ioi_comp_add (fun s => sharpConst d *
            volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d)) _).symm
      _ ≤ _ := hmono
      _ ≤ _ := hstep
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hK, hω])
  have hlim : Tendsto (fun h => ENNReal.ofReal ((∫ x, gradNorm ψ x) +
      modulus (gradNorm ψ) h * K1)) (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (∫ x, gradNorm ψ x))) := by
    have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := ∫ x, gradNorm ψ x)).add
      ((tendsto_modulus hgc hgcs).mul_const K1))
    simpa using this
  exact ge_of_tendsto hlim hev

/-- **Smooth case of the sharp `p = 1` Sobolev estimate (conditional on Brunn--Minkowski).** -/
theorem sharp_layer_bound (hd : 2 ≤ d)
    (BM : ∀ A B : Set (Vec d), IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
      volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d))
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (d : ℝ≥0∞) * volume (euclideanBall (0 : Vec d) 1) ^ ((1 : ℝ) / d) *
        ∫⁻ s in Ioi (0 : ℝ), volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) ≤
      ∫⁻ x, ENNReal.ofReal (gradNorm ψ x) := by
  have hgc := continuous_gradNorm hψ
  have hgcs := hasCompactSupport_gradNorm hc
  have hf := continuous_abs_comp hψ.continuous
  have hfc := hasCompactSupport_abs_comp hc
  have hgi : Integrable (gradNorm ψ) := hgc.integrable_of_hasCompactSupport hgcs
  rw [← ofReal_integral_eq_lintegral_ofReal hgi
    (Eventually.of_forall fun x => vecEuclideanNorm_nonneg _)]
  change sharpConst d * _ ≤ _
  have hanti : Antitone fun s : ℝ => volume {x | s ≤ |ψ x|} :=
    fun a b hab => measure_mono fun x hx => le_trans hab hx
  have hmeas0 : Measurable fun s : ℝ => volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) :=
    hanti.measurable.pow_const _
  have hmeas : Measurable fun s : ℝ => sharpConst d *
      volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d) := hmeas0.const_mul _
  rw [← lintegral_const_mul _ hmeas0, ← lintegral_indicator measurableSet_Ioi]
  have hsup : (Ioi (0 : ℝ)).indicator (fun s : ℝ => sharpConst d *
      volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d)) = fun s => ⨆ n : ℕ,
      (Ioi (1 / ((n : ℝ) + 1))).indicator (fun s : ℝ => sharpConst d *
        volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d)) s := by
    ext s
    by_cases hs : 0 < s
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
      rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
      refine le_antisymm ?_ (iSup_le fun m => indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le))
      refine le_trans (indicator_of_mem (show s ∈ Ioi (1 / ((n : ℝ) + 1)) from hn)
        (fun s : ℝ => sharpConst d * volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d))).ge
        (le_iSup (fun n : ℕ => (Ioi (1 / ((n : ℝ) + 1))).indicator (fun s : ℝ => sharpConst d *
        volume {x | s ≤ |ψ x|} ^ (((d : ℝ) - 1) / d)) s) n)
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
      symm
      refine le_antisymm (iSup_le fun n => ?_) (zero_le)
      rw [indicator_of_notMem]
      intro hmem
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact hs (this.trans hmem)
  rw [hsup, lintegral_iSup]
  · refine iSup_le fun n => ?_
    rw [lintegral_indicator measurableSet_Ioi]
    exact sharp_tail_bound hd BM hψ hc (by positivity)
  · exact fun n => hmeas.indicator measurableSet_Ioi
  · intro m n hmn s
    refine indicator_le_indicator_of_subset (Ioi_subset_Ioi ?_) (fun _ => zero_le) s
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

end Limit

end PDE.SobolevSharp
