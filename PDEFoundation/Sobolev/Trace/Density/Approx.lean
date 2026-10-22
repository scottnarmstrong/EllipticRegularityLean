module

public import PDEFoundation.Sobolev.Trace.Density.Core

/-!
# Approximation of an extended `W^{1,p}` pair by translated mollifications

See `Core.lean` for the idea.  The main result is `exists_smooth_approx_of_weak`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal Convolution

variable {d : ℕ}

theorem aestronglyMeasurable_of_coords {F : Vec d → Vec d} {μ : Measure (Vec d)}
    (h : ∀ i, AEStronglyMeasurable (fun x => F x i) μ) : AEStronglyMeasurable F μ :=
  (aemeasurable_pi_iff.2 fun i => (h i).aemeasurable).aestronglyMeasurable

theorem continuous_classicalGradient_apply {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) : Continuous fun x => classicalGradient φ x i := by
  simpa only [classicalGradient_apply] using
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Translate-and-mollify approximation of an extended pair. -/
theorem exists_smooth_approx_of_weak {Ω : Set (Vec d)} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {p : ℝ} (hp : 1 ≤ p) {W : Vec d → ℝ} {G : Vec d → Vec d}
    {O : Set (Vec d)} (hO : IsOpen O) (hW : MemLp W (ENNReal.ofReal p) volume)
    (hG : ∀ i, MemLp (fun x => G x i) (ENNReal.ofReal p) volume)
    (hweak : HasWeakGradientOn O W G) (e : Vec d) {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hcov : ∀ τ : ℝ, 0 < τ → τ < τ₀ → ∀ x ∈ closure Ω, x + τ • e ∈ O)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      w1pPairNorm Ω p (φ - W) (classicalGradient φ - G) < ε := by
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hqTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  -- translation errors
  let T : ℝ → ℝ≥0∞ := fun τ =>
    eLpNorm (fun x => W (x + τ • e) - W x) (ENNReal.ofReal p) volume +
      ∑ i, eLpNorm (fun x => G (x + τ • e) i - G x i) (ENNReal.ofReal p) volume
  have hT : Tendsto T (𝓝 0) (𝓝 0) := by
    have hshift : Tendsto (fun τ : ℝ => τ • e) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun τ : ℝ => τ • e := continuous_id.smul continuous_const
      have := hc.tendsto 0
      rwa [zero_smul] at this
    have h0 := (tendsto_eLpNorm_comp_add_sub hq hqTop hW).comp hshift
    have hi := fun i => (tendsto_eLpNorm_comp_add_sub hq hqTop (hG i)).comp hshift
    have := h0.add (tendsto_finsetSum Finset.univ fun i _ => hi i)
    simpa [T, Function.comp_def] using this
  have hεh : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨τ, hτ0, hτ1, hTτ⟩ : ∃ τ : ℝ, 0 < τ ∧ τ < τ₀ ∧ T τ < ε / 2 := by
    have h1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), T τ < ε / 2 :=
      (hT.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hεh)
    have h2 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ < τ₀ := by
      filter_upwards [Ioo_mem_nhdsGT hτ₀] with τ hτ using hτ
    obtain ⟨τ, h⟩ := (h1.and h2).exists
    exact ⟨τ, h.2.1, h.2.2, h.1⟩
  set v : Vec d := τ • e with hv
  have hCc : IsCompact ((fun x => x + v) '' closure Ω) :=
    hΩb.isCompact_closure.image (continuous_id.add continuous_const)
  have hCO : (fun x => x + v) '' closure Ω ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcov τ hτ0 hτ1 x hx
  obtain ⟨δ₀, hδ₀, hδ₀O⟩ := hCc.exists_cthickening_subset_open hO hCO
  -- mollification scales
  let a : ℕ → ℝ := fun n => min δ₀ 1 * unitConvexApproxScale n
  have hmin : 0 < min δ₀ 1 := lt_min hδ₀ one_pos
  have ha : ∀ n, 0 < a n := fun n => mul_pos hmin (unitConvexApproxScale_pos n)
  have ha1 : ∀ n, a n ≤ 1 := fun n =>
    (mul_le_of_le_one_right hmin.le (unitConvexApproxScale_le_one n)).trans (min_le_right _ _)
  have haδ : ∀ n, a n ≤ δ₀ := fun n =>
    (mul_le_of_le_one_right hmin.le (unitConvexApproxScale_le_one n)).trans (min_le_left _ _)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa using tendsto_unitConvexApproxScale_zero.const_mul (min δ₀ 1)
  let E : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (wholeSpaceMollify (a n) W - W) (ENNReal.ofReal p) volume +
      ∑ i, eLpNorm (wholeSpaceMollify (a n) (fun x => G x i) - fun x => G x i)
        (ENNReal.ofReal p) volume
  have hE : Tendsto E atTop (𝓝 0) := by
    have h0 := tendsto_eLpNorm_wholeSpaceMollify_sub hq hqTop hW ha ha1 ha0
    have hi := fun i => tendsto_eLpNorm_wholeSpaceMollify_sub hq hqTop (hG i) ha ha1 ha0
    simpa [E] using h0.add (tendsto_finsetSum Finset.univ fun i _ => hi i)
  obtain ⟨n, hn⟩ : ∃ n, E n < ε / 2 := (hE.eventually (Iio_mem_nhds hεh)).exists
  -- the approximant
  have hMW := contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) hq hqTop hW
  have hMG := fun i => contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) hq hqTop
    (hG i)
  let φ : Vec d → ℝ := fun x => wholeSpaceMollify (a n) W (x + v)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hMW.1.comp (contDiff_id.add contDiff_const)
  have hgrad : ∀ x ∈ closure Ω, ∀ i, classicalGradient φ x i =
      wholeSpaceMollify (a n) (fun x => G x i) (x + v) := by
    intro x hx i
    have hfd : fderiv ℝ φ x = fderiv ℝ (wholeSpaceMollify (a n) W) (x + v) :=
      fderiv_comp_add_right v
    rw [classicalGradient_apply, hfd]
    refine euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn_local
      (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (ha n))
      (contDiff_scaledConvexApproxKernel hρ _) (hW.locallyIntegrable hq)
      (fun y hy => scaledUnitKernel_eq_zero_of_lt_norm (ha n) hy) ?_ (hweak i)
    intro y hy
    apply hδ₀O
    refine Metric.mem_cthickening_of_dist_le y (x + v) δ₀ _ ⟨x, hx, rfl⟩ ?_
    exact (Metric.mem_closedBall.1 hy).trans (haδ n)
  refine ⟨φ, hφ, ?_⟩
  have hvalue : eLpNorm (φ - W) (ENNReal.ofReal p) (volumeOn Ω) ≤
      eLpNorm (wholeSpaceMollify (a n) W - W) (ENNReal.ofReal p) volume +
        eLpNorm (fun x => W (x + v) - W x) (ENNReal.ofReal p) volume := by
    refine eLpNorm_restrict_le_of_decomp hΩm hq v (fun x _ => ?_)
      ((hMW.1.continuous.aestronglyMeasurable).sub hW.aestronglyMeasurable)
    simp only [Pi.sub_apply, φ]; ring
  have hcoord : ∀ i, eLpNorm (fun x => (classicalGradient φ - G) x i) (ENNReal.ofReal p)
      (volumeOn Ω) ≤
      eLpNorm (wholeSpaceMollify (a n) (fun x => G x i) - fun x => G x i) (ENNReal.ofReal p)
        volume + eLpNorm (fun x => G (x + v) i - G x i) (ENNReal.ofReal p) volume := by
    intro i
    refine eLpNorm_restrict_le_of_decomp hΩm hq v (fun x hx => ?_)
      ((hMG i).1.continuous.aestronglyMeasurable.sub (hG i).aestronglyMeasurable)
    simp only [Pi.sub_apply]
    rw [hgrad x (subset_closure hx) i]; ring
  have hsum : pairSeminorm (volumeOn Ω) (ENNReal.ofReal p) (φ - W) (classicalGradient φ - G) ≤
      E n + T τ := by
    unfold pairSeminorm
    calc _ ≤ _ := add_le_add hvalue (Finset.sum_le_sum fun i _ => hcoord i)
      _ = E n + T τ := by
        simp only [E, T, Finset.sum_add_distrib, hv]; ring
  have hmeas : AEStronglyMeasurable (classicalGradient φ - G) (volumeOn Ω) := by
    refine aestronglyMeasurable_of_coords fun i => ?_
    exact ((continuous_classicalGradient_apply hφ i).aestronglyMeasurable).sub
      (hG i).aestronglyMeasurable.restrict
  calc w1pPairNorm Ω p (φ - W) (classicalGradient φ - G)
      ≤ pairSeminorm (volumeOn Ω) (ENNReal.ofReal p) (φ - W) (classicalGradient φ - G) :=
        w1pPairNorm_le_pairSeminorm hp _ hmeas
    _ ≤ E n + T τ := hsum
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hn hTτ
    _ = ε := ENNReal.add_halves ε

end PDE.TraceLane
