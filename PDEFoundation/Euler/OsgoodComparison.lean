module

public import PDEFoundation.Euler.OsgoodFixed

/-!
# Osgood comparison at a fixed exponent

`osgood_bound`: `0 ≤ y ≤ C` integrable on `[s, t₀]` with `y t ≤ ∫_s^t a y^(1-1/p)` gives
`y t ≤ (a (t-s)/p)^p`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

/-- Integrability of `a * y^r` for a bounded nonnegative integrable `y`. -/
theorem osgood_integrand_integrable {y : ℝ → ℝ} {s t₀ a C r : ℝ} (hst : s ≤ t₀) (hr : 0 ≤ r)
    (hy0 : ∀ t ∈ Icc s t₀, 0 ≤ y t) (hyC : ∀ t ∈ Icc s t₀, y t ≤ C)
    (hyi : IntervalIntegrable y volume s t₀) :
    IntervalIntegrable (fun τ => a * y τ ^ r) volume s t₀ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hst] at hyi ⊢
  have hm : AEStronglyMeasurable (fun τ => a * y τ ^ r) (volume.restrict (Icc s t₀)) :=
    (aestronglyMeasurable_const.mul (hyi.aestronglyMeasurable.aemeasurable.pow_const r).aestronglyMeasurable)
  refine Integrable.mono' (g := fun _ => |a| * max C 1 ^ r) (integrableOn_const (by simp)) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hy0 τ hτ) r)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
  exact Real.rpow_le_rpow (hy0 τ hτ) ((hyC τ hτ).trans (le_max_left _ _)) hr

/-- **Osgood comparison.** -/
theorem osgood_bound {y : ℝ → ℝ} {s t₀ a C p : ℝ} (hp : 1 < p) (ha : 0 ≤ a)
    (hy0 : ∀ t ∈ Icc s t₀, 0 ≤ y t) (hyC : ∀ t ∈ Icc s t₀, y t ≤ C)
    (hyi : IntervalIntegrable y volume s t₀)
    (h : ∀ t ∈ Icc s t₀, y t ≤ ∫ τ in s..t, a * y τ ^ (1 - p⁻¹)) :
    ∀ t ∈ Icc s t₀, y t ≤ (a * (t - s) / p) ^ p := by
  intro t₁ ht₁
  have hst : s ≤ t₀ := ht₁.1.trans ht₁.2
  have hp0 : 0 < p := by linarith
  have hq : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hq0 : 0 < p⁻¹ := inv_pos.2 hp0
  set r : ℝ := 1 - p⁻¹ with hr
  have hr0 : 0 < r := by linarith
  have hr1 : r ≤ 1 := by linarith
  set g : ℝ → ℝ := fun τ => a * y τ ^ r with hg
  have hgi : IntervalIntegrable g volume s t₀ :=
    osgood_integrand_integrable hst hr0.le hy0 hyC hyi
  set Z : ℝ → ℝ := fun t => ∫ τ in s..t, g τ with hZ
  have hZc : ContinuousOn Z (Icc s t₀) := by
    have := intervalIntegral.continuousOn_primitive_interval (by rw [Set.uIcc_of_le hst]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hst).1 hgi)
    rwa [Set.uIcc_of_le hst] at this
  have hZ0 : ∀ t ∈ Icc s t₀, 0 ≤ Z t := by
    intro t ht
    refine intervalIntegral.integral_nonneg ht.1 (fun τ hτ => ?_)
    exact mul_nonneg ha (Real.rpow_nonneg (hy0 τ ⟨hτ.1, hτ.2.trans ht.2⟩) r)
  have hyZ : ∀ t ∈ Icc s t₀, y t ≤ Z t := h
  -- main barrier estimate
  have key : ∀ δ : ℝ, 0 < δ → ∀ t ∈ Icc s t₀,
      Z t + δ ≤ (δ ^ p⁻¹ + a * (t - s) / p) ^ p := by
    intro δ hδ
    set c : ℝ → ℝ := fun τ => δ ^ p⁻¹ + a * (τ - s) / p with hc
    set Φ : ℝ → ℝ := fun τ => c τ ^ p with hΦ
    have hcpos : ∀ τ ∈ Icc s t₀, δ ^ p⁻¹ ≤ c τ := by
      intro τ hτ
      have : 0 ≤ a * (τ - s) / p := div_nonneg (mul_nonneg ha (sub_nonneg.2 hτ.1)) hp0.le
      simp only [hc]; linarith
    have hΦδ : ∀ τ ∈ Icc s t₀, δ ≤ Φ τ := by
      intro τ hτ
      have h1 : δ ^ p⁻¹ ≤ c τ := hcpos τ hτ
      have := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) h1 hp0.le
      rwa [← Real.rpow_mul hδ.le, inv_mul_cancel₀ hp0.ne', Real.rpow_one] at this
    have hΦc : ContinuousOn Φ (Icc s t₀) := by
      refine ContinuousOn.rpow_const (by fun_prop) ?_
      intro τ hτ; right; exact hp0.le
    set D : ℝ → ℝ := fun τ => Z τ + δ - Φ τ with hD
    set f : ℝ → ℝ := fun τ => max (D τ) 0 with hf
    have hfc : ContinuousOn f (Icc s t₀) :=
      ContinuousOn.sup ((hZc.add continuousOn_const).sub hΦc) continuousOn_const
    have hf0 : ∀ τ ∈ Icc s t₀, 0 ≤ f τ := fun τ _ => le_max_right _ _
    have hZr : ContinuousOn (fun τ => Z τ ^ r) (Icc s t₀) :=
      hZc.rpow_const (fun τ _ => Or.inr hr0.le)
    have hΦr : ContinuousOn (fun τ => Φ τ ^ r) (Icc s t₀) :=
      hΦc.rpow_const (fun τ _ => Or.inr hr0.le)
    set L : ℝ := a * (r * δ ^ (r - 1)) with hL
    have hL0 : 0 ≤ L := mul_nonneg ha (mul_nonneg hr0.le (Real.rpow_nonneg hδ.le _))
    have hineq : ∀ t ∈ Icc s t₀, f t ≤ L * ∫ τ in s..t, f τ := by
      intro t ht
      have hsub : Icc s t ⊆ Icc s t₀ := Icc_subset_Icc_right ht.2
      have hII : ∀ {F : ℝ → ℝ}, ContinuousOn F (Icc s t₀) → IntervalIntegrable F volume s t :=
        fun hF => (hF.mono hsub).intervalIntegrable_of_Icc ht.1
      have hbar := barrier_integral (s := s) (a := a) (p := p) (δ := δ) hp ha hδ t ht.1
      -- bound on Z
      have hZle : Z t ≤ ∫ τ in s..t, a * Z τ ^ r := by
        have hgt : IntervalIntegrable g volume s t := hgi.mono_set (by
          rw [Set.uIcc_of_le hst, Set.uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
        refine intervalIntegral.integral_mono_on ht.1 hgt
          ((continuousOn_const.mul hZr).mono hsub |>.intervalIntegrable_of_Icc ht.1) ?_
        intro τ hτ
        have hτ' : τ ∈ Icc s t₀ := hsub hτ
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hy0 τ hτ') (hyZ τ hτ') hr0.le) ha
      have hstep : ∀ τ ∈ Icc s t,
          a * Z τ ^ r - a * Φ τ ^ r ≤ L * f τ := by
        intro τ hτ
        have hτ' : τ ∈ Icc s t₀ := hsub hτ
        have hZ0' := hZ0 τ hτ'
        rw [← mul_sub]
        by_cases hcase : Φ τ ≤ Z τ + δ
        · have h1 := rpow_sub_rpow_le hr0.le hr1 hδ (hΦδ τ hτ') hcase
          have h2 : Z τ ^ r ≤ (Z τ + δ) ^ r :=
            Real.rpow_le_rpow hZ0' (by linarith) hr0.le
          have h3 : f τ = Z τ + δ - Φ τ := by
            simp only [hf, hD]; exact max_eq_left (by linarith)
          rw [h3, hL, mul_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith) ha
        · push Not at hcase
          have h2 : Z τ ^ r ≤ Φ τ ^ r :=
            Real.rpow_le_rpow hZ0' (by linarith) hr0.le
          have := hf0 τ hτ'
          have : 0 ≤ L * f τ := mul_nonneg hL0 this
          have : a * (Z τ ^ r - Φ τ ^ r) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ha (by linarith)
          linarith
      have hI1 : IntervalIntegrable (fun τ => a * Z τ ^ r) volume s t :=
        (continuousOn_const.mul hZr).mono hsub |>.intervalIntegrable_of_Icc ht.1
      have hI2 : IntervalIntegrable (fun τ => a * Φ τ ^ r) volume s t :=
        (continuousOn_const.mul hΦr).mono hsub |>.intervalIntegrable_of_Icc ht.1
      have hI3 : IntervalIntegrable (fun τ => L * f τ) volume s t :=
        (continuousOn_const.mul hfc).mono hsub |>.intervalIntegrable_of_Icc ht.1
      have hint := intervalIntegral.integral_mono_on ht.1 (hI1.sub hI2) hI3 hstep
      have hLf : ∫ τ in s..t, L * f τ = L * ∫ τ in s..t, f τ :=
        intervalIntegral.integral_const_mul L f
      have hbar' : ∫ τ in s..t, a * Φ τ ^ r = Φ t - δ := by
        simpa [hΦ, hc, hr] using hbar
      rw [intervalIntegral.integral_sub hI1 hI2, hbar', hLf] at hint
      have hDt : D t ≤ L * ∫ τ in s..t, f τ := by
        simp only [hD]; linarith
      exact max_le hDt (mul_nonneg hL0 (intervalIntegral.integral_nonneg ht.1
        (fun τ hτ => hf0 τ ⟨hτ.1, hτ.2.trans ht.2⟩)))
    have hz := gronwall_eq_zero hL0 hfc hf0 hineq
    intro t ht
    have := hz t ht
    have h2 : D t ≤ 0 := by
      have := le_max_left (D t) 0
      simp only [hf] at *
      linarith
    simp only [hD, hΦ, hc] at h2
    linarith
  -- δ → 0
  set k : ℝ := a * (t₁ - s) / p with hk
  have hcont : Continuous fun δ : ℝ => (δ ^ p⁻¹ + k) ^ p := by
    refine Continuous.rpow_const ((Real.continuous_rpow_const hq0.le).add continuous_const) ?_
    intro x; right; exact hp0.le
  have hlim : Tendsto (fun δ : ℝ => (δ ^ p⁻¹ + k) ^ p) (𝓝[>] 0) (𝓝 (k ^ p)) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Real.zero_rpow hq0.ne'] using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have h1 := key δ hδ t₁ ht₁
  have h2 := hyZ t₁ ht₁
  have h3 : 0 < δ := hδ
  simp only [hZ] at h1 h2
  linarith

end PDE
