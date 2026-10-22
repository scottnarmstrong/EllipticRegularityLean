/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerAux

/-! # Reverse Hölder step for positive powers on general nested cylinders -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ}

/-- Size of the cutoff constants in terms of the smallest gap. -/
theorem cutoff_Z_bound {B g δ1 δ2 δ3 : ℝ} (hB : 0 ≤ B) (hg : 0 < g) (hg1 : g ≤ 1) (h1 : g ≤ δ1)
    (h2 : g ≤ δ2) (h3 : g ≤ δ3) :
    1024 / δ1 ^ 2 + (B / δ2 + B / δ3) ≤ (1024 + 2 * B) / g ^ 2 := by
  have hg2 : 0 < g ^ 2 := by positivity
  have e1 : 1024 / δ1 ^ 2 ≤ 1024 / g ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) hg2 (pow_le_pow_left₀ hg.le h1 2)
  have e2 : ∀ δ : ℝ, g ≤ δ → B / δ ≤ B / g ^ 2 := by
    intro δ hδ
    have : g ^ 2 ≤ δ := (pow_le_of_le_one hg.le hg1 two_ne_zero).trans hδ
    exact div_le_div_of_nonneg_left hB hg2 this
  have := e2 _ h2
  have := e2 _ h3
  have e4 : (1024 + 2 * B) / g ^ 2 = 1024 / g ^ 2 + (B / g ^ 2 + B / g ^ 2) := by ring
  rw [e4]; linarith

/-- **Reverse Hölder step for `v^p`, `0 < p ≤ q`, between general nested cylinders** (Lebesgue
form): `(∬_{Q'} v^(pχ))^(1/χ) ≤ (C/g²) ∬_Q v^p`, `g` the smallest gap. -/
theorem holder_pos (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 ≤ Λ) (q : ℝ) (hq0 : 0 < q)
    (hq1 : q < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Λ a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ {r' ρ s s' t' t : ℝ}, 0 ≤ r' → r' < ρ → ρ ≤ 1 → -1 < s → s < s' →
        s' < t' → t' < t → t < 0 → ∀ p : ℝ, 0 < p → p ≤ q →
      (∫⁻ z in euclideanBall (0 : Vec d) r' ×ˢ Ioo s' t',
          ENNReal.ofReal ((u.toFun z + ε) ^ (p * (((d : ℝ) + 2) / d)))) ^ (1 / (((d : ℝ) + 2) / d)) ≤
        ENNReal.ofReal (C / (min (ρ - r') (min (s' - s) (t - t'))) ^ 2) *
          ∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t, ENNReal.ofReal ((u.toFun z + ε) ^ p) := by
  obtain ⟨Cd, hCd, hsob⟩ := sobolev_of_energy d hd
  obtain ⟨B, hB0, hcut⟩ := exists_powCutoff_pos (d := d)
  set χ : ℝ := ((d : ℝ) + 2) / d with hχ
  set M0 : ℝ := q / (1 - q) + 1 with hM0
  set k : ℝ := M0 * (2 + 2 * M0 * Λ) + 2 with hk
  set cd : ℝ := (Cd ^ (1 / χ)).toReal with hcd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hχ0 : 0 < χ := by rw [hχ]; positivity
  have hq1' : 0 < 1 - q := by linarith
  have hM1 : 1 ≤ M0 := by rw [hM0]; have : 0 ≤ q / (1 - q) := by positivity
                          linarith
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hcd0 : 0 ≤ cd := ENNReal.toReal_nonneg
  set C₀ : ℝ := max 1 (cd * k * (1024 + 2 * B)) with hC₀
  refine ⟨C₀, le_max_left _ _, ?_⟩
  intro a ha u hu hu0 ε hε r' ρ s s' t' t hr' hr'ρ hρ1 hs1 hss' hst hlt ht0 p hp hpq
  have hp1 : p < 1 := hpq.trans_lt hq1
  set g : ℝ := min (ρ - r') (min (s' - s) (t - t')) with hg
  have hg0 : 0 < g := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hg1 : g ≤ 1 := (min_le_left _ _).trans (by linarith)
  have hgr : g ≤ ρ - r' := min_le_left _ _
  have hgs : g ≤ s' - s := (min_le_right _ _).trans (min_le_left _ _)
  have hgt : g ≤ t - t' := (min_le_right _ _).trans (min_le_right _ _)
  set Q : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) ρ ×ˢ Ioo s t with hQ
  have hQm : MeasurableSet Q := (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hρU : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (hr'.trans hr'ρ.le) hρ1
  have hQU : Q ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono hρU (fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
  set R : ℝ≥0∞ := ∫⁻ z in Q, ENNReal.ofReal ((u.toFun z + ε) ^ p) with hR
  have hC₀1 : 1 ≤ C₀ := le_max_left _ _
  by_cases hRtop : R = ⊤
  · rw [hRtop, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (div_pos (by linarith) (pow_pos hg0 2))).ne'
  obtain ⟨hPint, hPeq⟩ := integrable_indicator_vr u hu0 hε p hQm hQU hRtop
  obtain ⟨η, hc, hlo, hhi, h1⟩ := hcut hρU hr' hr'ρ hss' hst hlt
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hfin : volume (euclideanBall (0 : Vec d) 1) ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  obtain ⟨hS, hG⟩ := energy_pos hU ha u hu hu0 hΛ hc hp hp1 hε hPint hs1
    (hss'.trans (hst.trans hlt)) ht0 hlo hhi
  -- constants
  set X : ℝ := 1024 / (ρ - r') ^ 2 with hX
  set T : ℝ := B / (s' - s) + B / (t - t') with hT
  have hX0 : 0 ≤ X := by positivity
  have hT0 : 0 ≤ T := by
    have : 0 < s' - s := by linarith
    have : 0 < t - t' := by linarith
    positivity
  have hZ : X + T ≤ (1024 + 2 * B) / g ^ 2 := by
    have := cutoff_Z_bound hB0 hg0 hg1 hgr hgs hgt
    simpa [hX, hT, add_assoc] using this
  have hm : |p| / (1 - p) ≤ M0 := by
    rw [abs_of_pos hp, hM0]
    have h1p : 0 < 1 - p := by linarith
    have : p / (1 - p) ≤ q / (1 - q) := by
      rw [div_le_div_iff₀ h1p hq1']; linarith
    linarith
  obtain ⟨hb1, hb2⟩ := const_bound hp.ne' hp1 hΛ hX0 hT0 hm
  set Z : ℝ := X + T with hZdef
  set Kz : ℝ := k * Z with hKz
  have hZ0 : 0 ≤ Z := by positivity
  have hKz0 : 0 ≤ Kz := by positivity
  have hS1 : 2 * T + 2 * |p| * Λ * X / (1 - p) ≤ Kz := by
    refine hb1.trans ?_
    have : 2 + 2 * M0 * Λ ≤ k := by
      rw [hk]
      have h5 : 0 ≤ 2 + 2 * M0 * Λ := by positivity
      have h6 := mul_nonneg (sub_nonneg.2 hM1) h5
      linarith
    exact mul_le_mul_of_nonneg_right this hZ0
  have hG1 : p ^ 2 / 2 * ((2 * T / |p| + 2 * Λ * X / (1 - p)) / ((1 - p) / 2)) + 2 * X ≤ Kz :=
    hb2
  have hGb0 : 0 ≤ (2 * T / |p| + 2 * Λ * X / (1 - p)) / ((1 - p) / 2) := by
    have : 0 < 1 - p := by linarith
    positivity
  have hconv : ∀ c : ℝ, 0 ≤ c → ENNReal.ofReal (c * ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      Q.indicator (fun z => (u.toFun z + ε) ^ p) z) = ENNReal.ofReal c * R := by
    intro c hc0
    rw [hPeq, ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hRtop]
  rw [hconv _ (by have := hc.hT; have := hc.hX; positivity)] at hG
  have hSnn : 0 ≤ 2 * T + 2 * |p| * Λ * X / (1 - p) := by
    have : 0 < 1 - p := by linarith
    positivity
  have hS' : ∀ᵐ τ ∂(volume.restrict (Ioo s t)),
      ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ p) ≤
        ENNReal.ofReal Kz * R := by
    filter_upwards [hS] with τ h
    refine h.trans ?_
    rw [hconv _ hSnn]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hS1) le_rfl
  have hPl : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ p) z) ≤ R :=
    (lintegral_indicator_vr hQm hQU _).le
  have hJI : Ioo s t ⊆ Ioc (-1 : ℝ) 0 := fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmain := hsob hU hfin u measurableSet_Ioo hJI hu0 hc hp1 hp.ne' hε
    (ENNReal.ofReal Kz * R) _ R hS' hG hPl
  set M : ℝ≥0∞ := ENNReal.ofReal Kz * R with hMdef
  have hD : ENNReal.ofReal (p ^ 2 / 2) * (ENNReal.ofReal
        ((2 * T / |p| + 2 * Λ * X / (1 - p)) / ((1 - p) / 2)) * R) +
      ENNReal.ofReal (2 * X) * R ≤ M := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← add_mul,
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) hGb0) (by positivity)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hG1) le_rfl
  have hmain' : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioo s t, ENNReal.ofReal
      (η z ^ (2 * ((d : ℝ) + 2) / d) * (u.toFun z + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      Cd * M ^ (2 / (d : ℝ)) * M := by
    refine hmain.trans ?_
    have h2d : 0 ≤ 2 / (d : ℝ) := by positivity
    have hSM : (ENNReal.ofReal Kz * R) ^ (2 / (d : ℝ)) ≤ M ^ (2 / (d : ℝ)) := le_rfl
    exact mul_le_mul' (mul_le_mul' le_rfl hSM) hD
  have hQ'sub : euclideanBall (0 : Vec d) r' ×ˢ Ioo s' t' ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioo s t := by
    refine prod_mono ((euclideanBall_mono hr' hr'ρ.le).trans hρU) ?_
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  have hL : ∫⁻ z in euclideanBall (0 : Vec d) r' ×ˢ Ioo s' t',
      ENNReal.ofReal ((u.toFun z + ε) ^ (p * χ)) ≤ Cd * M ^ (2 / (d : ℝ)) * M := by
    refine le_trans (le_of_eq ?_) (le_trans (lintegral_mono_set hQ'sub) hmain')
    refine setLIntegral_congr_fun ((measurableSet_euclideanBall _ _).prod measurableSet_Ioo)
      fun z hz => ?_
    have : η z = 1 := h1 z ⟨hz.1, Ioo_subset_Icc_self hz.2⟩
    simp [this, hχ]
  have hstep := lintegral_pow_step hd hCd hL
  refine hstep.trans ?_
  have hCdt : Cd ^ (1 / χ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hCd
  have hcdeq : Cd ^ (1 / χ) = ENNReal.ofReal cd := (ENNReal.ofReal_toReal hCdt).symm
  rw [hcdeq, hMdef, ← mul_assoc, ← ENNReal.ofReal_mul hcd0]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hg2 : 0 < g ^ 2 := by positivity
  rw [le_div_iff₀ hg2]
  calc cd * Kz * g ^ 2 = cd * k * (Z * g ^ 2) := by rw [hKz]; ring
    _ ≤ cd * k * (1024 + 2 * B) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := (le_div_iff₀ hg2).1 hZ
        exact this
    _ ≤ C₀ := le_max_right _ _
    _ ≤ C₀ := le_rfl

end PDE.Parabolic.WeakHarnack
