module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Shift

/-!
# Friedland--Hayman: monotonicity of the mean of the ground state

For `τ₁ < τ₂` the Wronskian identity shows that the likelihood ratio `ψ_{τ₂} / ψ_{τ₁}` is
nondecreasing on `[τ₂, ∞)`.  Extending the squared ratio by `0` to the left of `τ₂` gives a
nondecreasing `ρ` with `ψ_{τ₂}² w 1_{(τ₂,∞)} = ρ ψ_{τ₁}² w`, and a Chebyshev-type argument gives
`gaussMean τ₁ ≤ gaussMean τ₂`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace BKP

theorem gpsi_nonneg_of_le {τ s : ℝ} (h : τ ≤ s) : 0 ≤ gpsi τ s := by
  rcases h.eq_or_lt with rfl | hlt
  · simp [ouSol_self]
  · exact (gpsi_pos hlt).le

/-- Wronskian of two ground states against the weight. -/
def gwron (τ₁ τ₂ s : ℝ) : ℝ := (gdpsi τ₂ s * gpsi τ₁ s - gpsi τ₂ s * gdpsi τ₁ s) * gaussW s

theorem hasDerivAt_gwron (τ₁ τ₂ s : ℝ) :
    HasDerivAt (gwron τ₁ τ₂)
      ((gaussBeta τ₁ - gaussBeta τ₂) * gpsi τ₁ s * gpsi τ₂ s * gaussW s) s :=
  hasDerivAt_ouWronskian (hasDerivAt_ouSol _ τ₁) (hasDerivAt_ouSolDeriv _ τ₁)
    (hasDerivAt_ouSol _ τ₂) (hasDerivAt_ouSolDeriv _ τ₂) s

theorem tendsto_gwron (τ₁ τ₂ : ℝ) : Tendsto (gwron τ₁ τ₂) atTop (𝓝 0) := by
  have h1 := ((polyBdd_gdpsi τ₂).mul (polyBdd_gpsi τ₁)).tendsto_mul_gaussW
  have h2 := ((polyBdd_gpsi τ₂).mul (polyBdd_gdpsi τ₁)).tendsto_mul_gaussW
  have := h1.sub h2
  rw [sub_self] at this
  refine this.congr fun s => ?_
  simp only [gwron]
  ring

theorem gwron_nonneg {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) {s₀ : ℝ} (hs₀ : τ₂ ≤ s₀) : 0 ≤ gwron τ₁ τ₂ s₀ := by
  have hβ : gaussBeta τ₁ ≤ gaussBeta τ₂ := gaussBeta_mono h.le
  have hanti : AntitoneOn (gwron τ₁ τ₂) (Ici s₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici s₀)
      (fun x _ => (hasDerivAt_gwron τ₁ τ₂ x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_gwron τ₁ τ₂ x).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [interior_Ici] at hx
    have hx' : τ₂ ≤ x := le_trans hs₀ (le_of_lt hx)
    rw [(hasDerivAt_gwron τ₁ τ₂ x).deriv]
    have h1 : 0 ≤ gpsi τ₁ x := gpsi_nonneg_of_le (le_trans h.le hx')
    have h2 : 0 ≤ gpsi τ₂ x := gpsi_nonneg_of_le hx'
    have h3 : (gaussBeta τ₁ - gaussBeta τ₂) ≤ 0 := by linarith
    have := mul_nonneg h1 h2
    have := mul_nonneg this (gaussW_pos x).le
    nlinarith
  refine le_of_tendsto (tendsto_gwron τ₁ τ₂) ?_
  filter_upwards [eventually_ge_atTop s₀] with t ht
  exact hanti (show s₀ ∈ Ici s₀ from le_rfl) (show t ∈ Ici s₀ from ht) ht

theorem ratio_monotoneOn {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) :
    MonotoneOn (fun s => gpsi τ₂ s / gpsi τ₁ s) (Ici τ₂) := by
  have hd : ∀ x ∈ Ici τ₂, HasDerivAt (fun s => gpsi τ₂ s / gpsi τ₁ s)
      ((gdpsi τ₂ x * gpsi τ₁ x - gpsi τ₂ x * gdpsi τ₁ x) / gpsi τ₁ x ^ 2) x := fun x hx =>
    (hasDerivAt_ouSol _ τ₂ x).div (hasDerivAt_ouSol _ τ₁ x)
      (gpsi_pos (lt_of_lt_of_le h hx)).ne'
  refine monotoneOn_of_deriv_nonneg (convex_Ici τ₂)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_)
  have hx' : x ∈ Ici τ₂ := interior_subset hx
  rw [(hd x hx').deriv]
  have hw := gwron_nonneg h (show τ₂ ≤ x from hx')
  have : 0 ≤ gdpsi τ₂ x * gpsi τ₁ x - gpsi τ₂ x * gdpsi τ₁ x :=
    (mul_nonneg_iff_of_pos_right (gaussW_pos x)).1 hw
  positivity

/-- The squared likelihood ratio, extended by `0` to the left of `τ₂`. -/
def ratioRho (τ₁ τ₂ s : ℝ) : ℝ := if τ₂ < s then (gpsi τ₂ s / gpsi τ₁ s) ^ 2 else 0

theorem ratioRho_nonneg (τ₁ τ₂ s : ℝ) : 0 ≤ ratioRho τ₁ τ₂ s := by
  unfold ratioRho
  split_ifs
  · positivity
  · exact le_rfl

theorem ratioRho_mono {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) : Monotone (ratioRho τ₁ τ₂) := by
  intro a b hab
  by_cases ha : τ₂ < a
  · have hb : τ₂ < b := lt_of_lt_of_le ha hab
    have hr := ratio_monotoneOn h (show a ∈ Ici τ₂ from ha.le) (show b ∈ Ici τ₂ from hb.le) hab
    have h0 : 0 ≤ gpsi τ₂ a / gpsi τ₁ a :=
      div_nonneg (gpsi_pos ha).le (gpsi_pos (lt_trans h ha)).le
    simp only [ratioRho, ha, hb, ite_true]
    exact pow_le_pow_left₀ h0 hr 2
  · have : ratioRho τ₁ τ₂ a = 0 := by simp [ratioRho, ha]
    rw [this]
    exact ratioRho_nonneg τ₁ τ₂ b

theorem indicator_eq_ratioRho_mul {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) (s : ℝ) :
    (Ioi τ₂).indicator (fun s => gpsi τ₂ s ^ 2 * gaussW s) s =
      ratioRho τ₁ τ₂ s * (gpsi τ₁ s ^ 2 * gaussW s) := by
  by_cases hs : τ₂ < s
  · have hne : gpsi τ₁ s ≠ 0 := (gpsi_pos (lt_trans h hs)).ne'
    rw [indicator_of_mem (show s ∈ Ioi τ₂ from hs)]
    simp only [ratioRho, hs, ite_true]
    field_simp
  · rw [indicator_of_notMem (show s ∉ Ioi τ₂ from hs)]
    simp [ratioRho, hs]

theorem gaussMean_le {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) : gaussMean τ₁ ≤ gaussMean τ₂ := by
  set m := gaussMean τ₁ with hm
  set ρ := ratioRho τ₁ τ₂ with hρdef
  have hρ : Monotone ρ := ratioRho_mono h
  set q : ℝ → ℝ := fun s => gpsi τ₁ s ^ 2 * gaussW s with hq
  have hq0 : ∀ s, 0 ≤ q s := fun s => mul_nonneg (sq_nonneg _) (gaussW_pos s).le
  have hP : ∀ s, (Ioi τ₂).indicator (fun s => gpsi τ₂ s ^ 2 * gaussW s) s = ρ s * q s :=
    indicator_eq_ratioRho_mul h
  have hB : ∀ s, (Ioi τ₂).indicator (fun s => s * gpsi τ₂ s ^ 2 * gaussW s) s =
      s * (ρ s * q s) := by
    intro s
    by_cases hs : τ₂ < s
    · have h1 := hP s
      rw [indicator_of_mem (show s ∈ Ioi τ₂ from hs)] at h1 ⊢
      rw [← h1]
      ring
    · have h1 := hP s
      rw [indicator_of_notMem (show s ∉ Ioi τ₂ from hs)] at h1 ⊢
      rw [← h1]
      simp
  -- the two integrands on `Ioi τ₁`
  have iA : IntegrableOn
      ((Ioi τ₂).indicator (fun s => gpsi τ₂ s ^ 2 * gaussW s)) (Ioi τ₁) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_gpsi_sq τ₂ τ₂)).integrableOn
  have iB : IntegrableOn
      ((Ioi τ₂).indicator (fun s => s * gpsi τ₂ s ^ 2 * gaussW s)) (Ioi τ₁) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_gpsi_mean τ₂ τ₂)).integrableOn
  have iq : IntegrableOn q (Ioi τ₁) := integrableOn_gpsi_sq τ₁ τ₁
  have isq : IntegrableOn (fun s => s * q s) (Ioi τ₁) :=
    (integrableOn_gpsi_mean τ₁ τ₁).congr_fun (fun s _ => by simp only [hq]; ring)
      measurableSet_Ioi
  have hint_f : IntegrableOn (fun s => ρ m * (s * q s - m * q s)) (Ioi τ₁) :=
    (isq.sub (iq.const_mul m)).const_mul (ρ m)
  have hint_g : IntegrableOn
      (fun s => (Ioi τ₂).indicator (fun s => s * gpsi τ₂ s ^ 2 * gaussW s) s -
        m * (Ioi τ₂).indicator (fun s => gpsi τ₂ s ^ 2 * gaussW s) s) (Ioi τ₁) :=
    iB.sub (iA.const_mul m)
  have hle := setIntegral_mono_on hint_f hint_g measurableSet_Ioi (fun s _ => by
    rw [hB s, hP s]
    have hc : 0 ≤ (s - m) * (ρ s - ρ m) := by
      rcases le_total m s with hms | hms
      · exact mul_nonneg (sub_nonneg.2 hms) (sub_nonneg.2 (hρ hms))
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hms) (sub_nonpos.2 (hρ hms))
    have := mul_nonneg hc (hq0 s)
    linarith)
  have hf0 : ∫ s in Ioi τ₁, ρ m * (s * q s - m * q s) = 0 := by
    rw [integral_const_mul, integral_sub isq (iq.const_mul m), integral_const_mul]
    have e : ∫ s in Ioi τ₁, s * q s = ∫ s in Ioi τ₁, s * gpsi τ₁ s ^ 2 * gaussW s :=
      setIntegral_congr_fun measurableSet_Ioi (fun s _ => by simp only [hq]; ring)
    have h2 := gaussMean_mul τ₁
    rw [e, ← h2]
    show ρ m * (m * (∫ s in Ioi τ₁, gpsi τ₁ s ^ 2 * gaussW s) -
      m * ∫ s in Ioi τ₁, gpsi τ₁ s ^ 2 * gaussW s) = 0
    ring
  have hg : ∫ s in Ioi τ₁, ((Ioi τ₂).indicator (fun s => s * gpsi τ₂ s ^ 2 * gaussW s) s -
        m * (Ioi τ₂).indicator (fun s => gpsi τ₂ s ^ 2 * gaussW s) s) =
      (∫ s in Ioi τ₂, s * gpsi τ₂ s ^ 2 * gaussW s) -
        m * ∫ s in Ioi τ₂, gpsi τ₂ s ^ 2 * gaussW s := by
    rw [integral_sub iB (iA.const_mul m), integral_const_mul,
      setIntegral_indicator measurableSet_Ioi, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.2 (Ioi_subset_Ioi h.le)]
  rw [hf0, hg] at hle
  rw [gaussMean, le_div_iff₀ (ground_integral_pos τ₂)]
  linarith

end BKP

open BKP

theorem gaussMean_mono : Monotone gaussMean := fun a b hab => by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact gaussMean_le hlt

end

end PDE.FHLane
