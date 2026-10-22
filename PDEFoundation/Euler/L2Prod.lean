module

public import PDEFoundation.Euler.L2Limit

/-!
# Products of `L²`-convergent sequences against a bounded weight

If `fₖ → F` and `gₖ → G` in `L²(μ)` and `β` is a bounded measurable weight then
`∫ β fₖ gₖ → ∫ β F G`.  This is the single continuity statement used for all the limits `a → 0` of the cross
terms (slice level on the cube and space-time level).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PDE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem abs_integral_weight_mul_le {β h G : α → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C) (hh : MemLp h 2 μ) (hG : MemLp G 2 μ) :
    |∫ x, β x * (h x * G x) ∂μ| ≤ C * ((eLpNorm h 2 μ).toReal * (eLpNorm G 2 μ).toReal) := by
  have hint : Integrable (fun x => h x * G x) μ := hh.integrable_mul hG
  have hint2 : Integrable (fun x => β x * (h x * G x)) μ :=
    hint.bdd_mul hβ (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have habs : MemLp (fun x => |h x|) 2 μ := by
    simpa using (memLp_norm_iff hh.aestronglyMeasurable).2 hh
  have habsG : MemLp (fun x => |G x|) 2 μ := by
    simpa using (memLp_norm_iff hG.aestronglyMeasurable).2 hG
  have hcs := abs_integral_mul_le_eLpNorm_two habs habsG
  have e1 : eLpNorm (fun x => |h x|) 2 μ = eLpNorm h 2 μ :=
    eLpNorm_congr_norm_ae habs.aestronglyMeasurable hh.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  have e2 : eLpNorm (fun x => |G x|) 2 μ = eLpNorm G 2 μ :=
    eLpNorm_congr_norm_ae habsG.aestronglyMeasurable hG.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  rw [e1, e2] at hcs
  have hint3 : Integrable (fun x => |h x| * |G x|) μ := by
    have := hint.abs
    simpa [abs_mul] using this
  calc |∫ x, β x * (h x * G x) ∂μ| ≤ ∫ x, |β x * (h x * G x)| ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => β x * (h x * G x))
    _ ≤ ∫ x, C * (|h x| * |G x|) ∂μ := by
        refine integral_mono_ae hint2.abs (hint3.const_mul C) ?_
        filter_upwards [hC] with x hx
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = C * ∫ x, |h x| * |G x| ∂μ := by rw [integral_const_mul]
    _ ≤ C * ((eLpNorm h 2 μ).toReal * (eLpNorm G 2 μ).toReal) := by
        refine mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) ?_) hC0
        exact hcs

theorem tendsto_integral_weight_mul_of_L2 {β : α → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C) {f g : ℕ → α → ℝ} {F G : α → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hF : MemLp F 2 μ) (hg : ∀ k, MemLp (g k) 2 μ) (hG : MemLp G 2 μ)
    (hfc : Tendsto (fun k => eLpNorm (f k - F) 2 μ) atTop (𝓝 0))
    (hgc : Tendsto (fun k => eLpNorm (g k - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, β x * (f k x * g k x) ∂μ) atTop (𝓝 (∫ x, β x * (F x * G x) ∂μ)) := by
  have hfc' : Tendsto (fun k => (eLpNorm (f k - F) 2 μ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp hfc
    simpa [Function.comp_def] using this
  have hgc' : Tendsto (fun k => (eLpNorm (g k - G) 2 μ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp hgc
    simpa [Function.comp_def] using this
  set nF := (eLpNorm F 2 μ).toReal
  set nG := (eLpNorm G 2 μ).toReal
  -- the bound
  have hbound : ∀ k, |∫ x, β x * (f k x * g k x) ∂μ - ∫ x, β x * (F x * G x) ∂μ| ≤
      C * ((nF + (eLpNorm (f k - F) 2 μ).toReal) * (eLpNorm (g k - G) 2 μ).toReal) +
        C * ((eLpNorm (f k - F) 2 μ).toReal * nG) := by
    intro k
    have hfk := hf k
    have hgk := hg k
    have hgd : MemLp (g k - G) 2 μ := hgk.sub hG
    have hfd : MemLp (f k - F) 2 μ := (hf k).sub hF
    have e : ∫ x, β x * (f k x * g k x) ∂μ - ∫ x, β x * (F x * G x) ∂μ =
        ∫ x, β x * (f k x * (g k - G) x) ∂μ + ∫ x, β x * ((f k - F) x * G x) ∂μ := by
      have i1 : Integrable (fun x => β x * (f k x * g k x)) μ :=
        (hfk.integrable_mul hgk).bdd_mul hβ (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
      have i2 : Integrable (fun x => β x * (F x * G x)) μ :=
        (hF.integrable_mul hG).bdd_mul hβ (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
      have i3 : Integrable (fun x => β x * (f k x * (g k - G) x)) μ :=
        (hfk.integrable_mul hgd).bdd_mul hβ (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
      have i4 : Integrable (fun x => β x * ((f k - F) x * G x)) μ :=
        (hfd.integrable_mul hG).bdd_mul hβ (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
      rw [← integral_sub i1 i2, ← integral_add i3 i4]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_integral_weight_mul_le hC0 hβ hC hfk hgd).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg) hC0
      have h1 : eLpNorm (f k) 2 μ ≤ eLpNorm F 2 μ + eLpNorm (f k - F) 2 μ := by
        calc eLpNorm (f k) 2 μ = eLpNorm (F + (f k - F)) 2 μ := by congr 1; funext x; simp
          _ ≤ eLpNorm F 2 μ + eLpNorm (f k - F) 2 μ := eLpNorm_add_le (by norm_num)
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hF.eLpNorm_ne_top, hfd.eLpNorm_ne_top⟩) h1
      rwa [ENNReal.toReal_add hF.eLpNorm_ne_top hfd.eLpNorm_ne_top] at this
    · exact abs_integral_weight_mul_le hC0 hβ hC hfd hG
  have hlim : Tendsto (fun k => C * ((nF + (eLpNorm (f k - F) 2 μ).toReal) *
        (eLpNorm (g k - G) 2 μ).toReal) + C * ((eLpNorm (f k - F) 2 μ).toReal * nG)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (nF + (eLpNorm (f k - F) 2 μ).toReal) *
        (eLpNorm (g k - G) 2 μ).toReal) atTop (𝓝 ((nF + 0) * 0)) :=
      (tendsto_const_nhds.add hfc').mul hgc'
    have h2 : Tendsto (fun k => (eLpNorm (f k - F) 2 μ).toReal * nG) atTop (𝓝 (0 * nG)) :=
      hfc'.mul tendsto_const_nhds
    have := (h1.const_mul C).add (h2.const_mul C)
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hlim
  rw [Real.dist_eq]
  exact hbound k

/-- Weighted limit with one factor fixed. -/
theorem tendsto_integral_weight_mul_left {β : α → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C) {f : ℕ → α → ℝ} {F g : α → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hF : MemLp F 2 μ) (hg : MemLp g 2 μ)
    (hfc : Tendsto (fun k => eLpNorm (f k - F) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, β x * (f k x * g x) ∂μ) atTop (𝓝 (∫ x, β x * (F x * g x) ∂μ)) := by
  refine tendsto_integral_weight_mul_of_L2 hC0 hβ hC (g := fun _ => g) hf hF (fun _ => hg) hg hfc ?_
  simp

end PDE
