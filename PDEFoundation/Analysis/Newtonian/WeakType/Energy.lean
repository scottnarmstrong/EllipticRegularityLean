module

public import PDEFoundation.Analysis.Newtonian.WeakType.EnergyBound

/-!
# `L²` energy bound for the Newton potential (internal lemma)

For smooth compactly supported `h`, `‖∇u_h‖_{L²} ≤ ‖h‖_{L²}`, and the Chebyshev corollary.  The
only external input is the representation statement (D2), `hD2`, taken as a hypothesis (the
statement `eq_newtonPotential_of_laplacian_eq_div`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem lintegral_gradient_newtonPotential_sq_le (hd : 0 < d)
    (hD2 : ∀ (w : Vec d → ℝ) (F : Vec d → Vec d), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) → w = newtonPotential F)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) :
    ∫⁻ x, ENNReal.ofReal (vecNormSq (classicalGradient (newtonPotential h) x)) ≤
      ∫⁻ x, ENNReal.ofReal (vecNormSq (h x)) := by
  obtain ⟨R₀, hR₀, hsupp⟩ := exists_tsupport_subset_euclideanBall hhc
  obtain ⟨M, hM⟩ := cutoff_energy_le hd hD2 hh hhc hR₀ hsupp
  have hu := contDiff_newtonPotential hd hh hhc
  set G : Vec d → Vec d := classicalGradient (newtonPotential h) with hG
  have hGc : Continuous G := continuous_classicalGradient hu
  set c : ℝ := max 1 (2 * R₀) with hc
  have hc0 : 0 < c := lt_max_of_lt_left one_pos
  set Rn : ℕ → ℝ := fun n => c + n with hRn
  have hRnpos : ∀ n, 0 < Rn n := fun n => by simp only [hRn]; positivity
  have hRnge : ∀ n, c ≤ Rn n := fun n => by simp only [hRn]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  set fn : ℕ → Vec d → ENNReal := fun n x =>
    ENNReal.ofReal (cutoff (Rn n) x ^ 2 * vecNormSq (G x)) with hfn
  have hfnm : ∀ n, Measurable (fn n) := fun n =>
    ENNReal.measurable_ofReal.comp (((contDiff_cutoff (hRnpos n)).continuous.pow 2).mul
      (continuous_vecDot_comp hGc hGc)).measurable
  have hfat := lintegral_liminf_le (μ := (volume : Measure (Vec d))) (u := atTop) hfnm
  -- pointwise liminf
  have hlim : ∀ x, liminf (fun n => fn n x) atTop = ENNReal.ofReal (vecNormSq (G x)) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, fn n x = ENNReal.ofReal (vecNormSq (G x)) := by
      have : ∀ᶠ n : ℕ in atTop, vecEuclideanNorm x < Rn n := by
        have h1 : Tendsto Rn atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
        exact h1.eventually_gt_atTop _
      filter_upwards [this] with n hn
      simp only [hfn, cutoff_eq_one (hRnpos n) hn]
      simp
    rw [Filter.liminf_congr hev, Filter.liminf_const]
  have hH2c : Continuous fun x => vecNormSq (h x) := continuous_vecDot_comp hh.continuous hh.continuous
  have hH2s : HasCompactSupport fun x => vecNormSq (h x) :=
    hasCompactSupport_of_field_zero hhc fun x hx => by simp [hx, vecNormSq, vecDot]
  have hiH : Integrable (fun x => vecNormSq (h x)) volume :=
    hH2c.integrable_of_hasCompactSupport hH2s
  have hHeq : ∫⁻ x, ENNReal.ofReal (vecNormSq (h x)) = ENNReal.ofReal (∫ x, vecNormSq (h x)) :=
    (ofReal_integral_eq_lintegral_ofReal hiH
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)).symm
  -- bound on each lintegral
  have hbound : ∀ n, ∫⁻ x, fn n x ≤
      ENNReal.ofReal ((∫ x, vecNormSq (h x)) + 4 * M / Rn n) := by
    intro n
    have hcc : Continuous fun x => cutoff (Rn n) x ^ 2 * vecNormSq (G x) :=
      ((contDiff_cutoff (hRnpos n)).continuous.pow 2).mul (continuous_vecDot_comp hGc hGc)
    have hcs : HasCompactSupport fun x => cutoff (Rn n) x ^ 2 * vecNormSq (G x) :=
      hasCompactSupport_of_cutoff_zero (hRnpos n) fun x hx => by simp [hx]
    have hint : Integrable (fun x => cutoff (Rn n) x ^ 2 * vecNormSq (G x)) volume :=
      hcc.integrable_of_hasCompactSupport hcs
    have : ∫⁻ x, fn n x = ENNReal.ofReal (∫ x, cutoff (Rn n) x ^ 2 * vecNormSq (G x)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))).symm
    rw [this]
    exact ENNReal.ofReal_le_ofReal (hM (Rn n) (hRnge n))
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal ((∫ x, vecNormSq (h x)) + 4 * M / Rn n))
      atTop (𝓝 (ENNReal.ofReal (∫ x, vecNormSq (h x)))) := by
    have h1 : Tendsto Rn atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 4 * M / Rn n) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h1
    have h3 := (tendsto_const_nhds (x := ∫ x, vecNormSq (h x))).add h2
    rw [add_zero] at h3
    exact (ENNReal.tendsto_ofReal h3)
  calc ∫⁻ x, ENNReal.ofReal (vecNormSq (G x))
      = ∫⁻ x, liminf (fun n => fn n x) atTop := by simp_rw [hlim]
    _ ≤ liminf (fun n => ∫⁻ x, fn n x) atTop := hfat
    _ ≤ liminf (fun n : ℕ => ENNReal.ofReal ((∫ x, vecNormSq (h x)) + 4 * M / Rn n)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
    _ = ENNReal.ofReal (∫ x, vecNormSq (h x)) := htend.liminf_eq
    _ = ∫⁻ x, ENNReal.ofReal (vecNormSq (h x)) := hHeq.symm

/-- Chebyshev: `|{ |∇u_h| > λ }| ≤ λ⁻² ∫ |h|²`. -/
theorem volume_gradient_newtonPotential_gt_le (hd : 0 < d)
    (hD2 : ∀ (w : Vec d → ℝ) (F : Vec d → Vec d), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) → w = newtonPotential F)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    {l : ℝ} (hl : 0 < l) :
    volume {x | l < vecEuclideanNorm (classicalGradient (newtonPotential h) x)} ≤
      ENNReal.ofReal (l⁻¹ ^ 2 * ∫ x, vecNormSq (h x)) := by
  have hu := contDiff_newtonPotential hd hh hhc
  have hGc := continuous_classicalGradient hu
  have hH2c : Continuous fun x => vecNormSq (h x) := continuous_vecDot_comp hh.continuous hh.continuous
  have hH2s : HasCompactSupport fun x => vecNormSq (h x) :=
    hasCompactSupport_of_field_zero hhc fun x hx => by simp [hx, vecNormSq, vecDot]
  have hiH : Integrable (fun x => vecNormSq (h x)) volume :=
    hH2c.integrable_of_hasCompactSupport hH2s
  have hHeq : ∫⁻ x, ENNReal.ofReal (vecNormSq (h x)) = ENNReal.ofReal (∫ x, vecNormSq (h x)) :=
    (ofReal_integral_eq_lintegral_ofReal hiH
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)).symm
  have hmeas : Measurable fun x => ENNReal.ofReal
      (vecNormSq (classicalGradient (newtonPotential h) x)) :=
    ENNReal.measurable_ofReal.comp (continuous_vecDot_comp hGc hGc).measurable
  have hsub : {x | l < vecEuclideanNorm (classicalGradient (newtonPotential h) x)} ⊆
      {x | ENNReal.ofReal (l ^ 2) ≤ ENNReal.ofReal
        (vecNormSq (classicalGradient (newtonPotential h) x))} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    refine ENNReal.ofReal_le_ofReal ?_
    have := vecEuclideanNorm_sq (classicalGradient (newtonPotential h) x)
    nlinarith [vecEuclideanNorm_nonneg (classicalGradient (newtonPotential h) x)]
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (volume : Measure (Vec d))) hmeas.aemeasurable (ENNReal.ofReal (l ^ 2))
  have hE := lintegral_gradient_newtonPotential_sq_le hd hD2 hh hhc
  have hl2 : (0 : ℝ) < l ^ 2 := by positivity
  have h1 : ENNReal.ofReal (l ^ 2) * volume {x | l < vecEuclideanNorm
      (classicalGradient (newtonPotential h) x)} ≤ ENNReal.ofReal (∫ x, vecNormSq (h x)) :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmarkov.trans (hE.trans_eq hHeq))
  calc volume {x | l < vecEuclideanNorm (classicalGradient (newtonPotential h) x)}
      = ENNReal.ofReal (l⁻¹ ^ 2) * (ENNReal.ofReal (l ^ 2) * volume {x | l < vecEuclideanNorm
          (classicalGradient (newtonPotential h) x)}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        have : l⁻¹ ^ 2 * l ^ 2 = 1 := by field_simp
        rw [this]
        simp
    _ ≤ ENNReal.ofReal (l⁻¹ ^ 2) * ENNReal.ofReal (∫ x, vecNormSq (h x)) := by gcongr
    _ = ENNReal.ofReal (l⁻¹ ^ 2 * ∫ x, vecNormSq (h x)) :=
        (ENNReal.ofReal_mul (by positivity)).symm

end

end PDE.NewtonWeakType
