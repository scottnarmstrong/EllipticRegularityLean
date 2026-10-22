/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerCorePos

/-! # Reverse Hölder step for negative powers on general nested cylinders -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ}

/-- **Reverse Hölder step for `v^r`, `r < 0`, between general nested cylinders** (Lebesgue form),
with a constant independent of `r`. -/
theorem holder_neg (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Λ a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∀ {r' ρ s s' : ℝ}, 0 ≤ r' → r' < ρ → ρ ≤ 1 → -1 < s → s < s' →
        s' ≤ 0 → ∀ r : ℝ, r < 0 →
      (∫⁻ z in euclideanBall (0 : Vec d) r' ×ˢ Ioc s' 0,
          ENNReal.ofReal ((u.toFun z + ε) ^ (r * (((d : ℝ) + 2) / d)))) ^ (1 / (((d : ℝ) + 2) / d)) ≤
        ENNReal.ofReal (C / (min (ρ - r') (s' - s)) ^ 2) *
          ∫⁻ z in euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0, ENNReal.ofReal ((u.toFun z + ε) ^ r) := by
  obtain ⟨Cd, hCd, hsob⟩ := sobolev_of_energy d hd
  obtain ⟨B, hB0, hcut⟩ := exists_powCutoff_neg (d := d)
  set χ : ℝ := ((d : ℝ) + 2) / d with hχ
  set M0 : ℝ := 1 with hM0
  set k : ℝ := M0 * (2 + 2 * M0 * Λ) + 2 with hk
  set cd : ℝ := (Cd ^ (1 / χ)).toReal with hcd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hχ0 : 0 < χ := by rw [hχ]; positivity
  have hk0 : 0 ≤ k := by rw [hk, hM0]; positivity
  have hcd0 : 0 ≤ cd := ENNReal.toReal_nonneg
  set C₀ : ℝ := max 1 (cd * k * (1024 + 2 * B)) with hC₀
  refine ⟨C₀, le_max_left _ _, ?_⟩
  intro a ha u hu hu0 ε hε r' ρ s s' hr' hr'ρ hρ1 hs1 hss' hs'0 r hr
  have hr1 : r < 1 := by linarith
  set g : ℝ := min (ρ - r') (s' - s) with hg
  have hg0 : 0 < g := lt_min (by linarith) (by linarith)
  have hg1 : g ≤ 1 := (min_le_left _ _).trans (by linarith)
  have hgr : g ≤ ρ - r' := min_le_left _ _
  have hgs : g ≤ s' - s := min_le_right _ _
  set Q : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) ρ ×ˢ Ioi s with hQ
  set Qr : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) ρ ×ˢ Ioc s 0 with hQr
  have hQm : MeasurableSet Q := (measurableSet_euclideanBall _ _).prod measurableSet_Ioi
  have hρU : euclideanBall (0 : Vec d) ρ ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (hr'.trans hr'ρ.le) hρ1
  have hQQr : Q ∩ (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) = Qr := by
    ext ⟨x, τ⟩
    simp only [hQ, hQr, mem_inter_iff, mem_prod, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨hx, hτ⟩, -, hτ2⟩; exact ⟨hx, hτ, hτ2.2⟩
    · rintro ⟨hx, hτ, hτ2⟩
      exact ⟨⟨hx, hτ⟩, hρU hx, by linarith, hτ2⟩
  set R : ℝ≥0∞ := ∫⁻ z in Qr, ENNReal.ofReal ((u.toFun z + ε) ^ r) with hR
  have hC₀1 : 1 ≤ C₀ := le_max_left _ _
  by_cases hRtop : R = ⊤
  · rw [hRtop, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (div_pos (by linarith) (pow_pos hg0 2))).ne'
  obtain ⟨hPint, hPeq⟩ := integrable_indicator_vr' u hu0 hε r hQm (by rw [hQQr]; exact hRtop)
  rw [hQQr] at hPeq
  obtain ⟨η, hc, hlo, h1⟩ := hcut hρU hr' hr'ρ hss'
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hfin : volume (euclideanBall (0 : Vec d) 1) ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  obtain ⟨hS, hG⟩ := energy_neg hU ha u hu hu0 hΛ hc hr hε hPint hs1 (by linarith) hlo
  set X : ℝ := 1024 / (ρ - r') ^ 2 with hX
  set T : ℝ := B / (s' - s) with hT
  have hX0 : 0 ≤ X := by positivity
  have hT0 : 0 ≤ T := by
    have : 0 < s' - s := by linarith
    positivity
  have hZ : X + T ≤ (1024 + 2 * B) / g ^ 2 := by
    have := cutoff_Z_bound hB0 hg0 hg1 hgr hgs hgs
    have h2 : 0 ≤ B / (s' - s) := by
      have : 0 < s' - s := by linarith
      positivity
    simp only [hX, hT] at *
    linarith
  have hm : |r| / (1 - r) ≤ M0 := by
    rw [abs_of_neg hr, hM0, div_le_one (by linarith)]; linarith
  obtain ⟨hb1, hb2⟩ := const_bound hr.ne hr1 hΛ hX0 hT0 hm
  set Z : ℝ := X + T with hZdef
  set Kz : ℝ := k * Z with hKz
  have hZ0 : 0 ≤ Z := by positivity
  have hKz0 : 0 ≤ Kz := by positivity
  have hS1 : 2 * T + 2 * |r| * Λ * X / (1 - r) ≤ Kz := by
    refine hb1.trans ?_
    have : 2 + 2 * M0 * Λ ≤ k := by rw [hk, hM0]; linarith
    exact mul_le_mul_of_nonneg_right this hZ0
  have hG1 : r ^ 2 / 2 * ((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) + 2 * X ≤ Kz :=
    hb2
  have hGb0 : 0 ≤ (2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2) := by
    have : 0 < 1 - r := by linarith
    positivity
  have hconv : ∀ c : ℝ, 0 ≤ c → ENNReal.ofReal (c * ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      Q.indicator (fun z => (u.toFun z + ε) ^ r) z) = ENNReal.ofReal c * R := by
    intro c hc0
    rw [hPeq, ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hRtop]
  rw [hconv _ (by have := hc.hT; have := hc.hX; positivity)] at hG
  have hSnn : 0 ≤ 2 * T + 2 * |r| * Λ * X / (1 - r) := by
    have : 0 < 1 - r := by linarith
    positivity
  have hS' : ∀ᵐ τ ∂(volume.restrict (Ioc s 0)),
      ∫⁻ x in euclideanBall (0 : Vec d) 1, ENNReal.ofReal (η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r) ≤
        ENNReal.ofReal Kz * R := by
    filter_upwards [hS] with τ h
    refine h.trans ?_
    rw [hconv _ hSnn]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hS1) le_rfl
  have hPl : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z) ≤ R := by
    rw [lintegral_indicator_vr' hQm, hQQr]
  have hJI : Ioc s 0 ⊆ Ioc (-1 : ℝ) 0 := Ioc_subset_Ioc hs1.le le_rfl
  have hmain := hsob hU hfin u measurableSet_Ioc hJI hu0 hc hr1 hr.ne hε
    (ENNReal.ofReal Kz * R) _ R hS' hG hPl
  set M : ℝ≥0∞ := ENNReal.ofReal Kz * R with hMdef
  have hD : ENNReal.ofReal (r ^ 2 / 2) * (ENNReal.ofReal
        ((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) * R) +
      ENNReal.ofReal (2 * X) * R ≤ M := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← add_mul,
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) hGb0) (by positivity)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hG1) le_rfl
  have hmain' : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s 0, ENNReal.ofReal
      (η z ^ (2 * ((d : ℝ) + 2) / d) * (u.toFun z + ε) ^ (r * (((d : ℝ) + 2) / d))) ≤
      Cd * M ^ (2 / (d : ℝ)) * M := by
    refine hmain.trans ?_
    have hSM : (ENNReal.ofReal Kz * R) ^ (2 / (d : ℝ)) ≤ M ^ (2 / (d : ℝ)) := le_rfl
    exact mul_le_mul' (mul_le_mul' le_rfl hSM) hD
  have hQ'sub : euclideanBall (0 : Vec d) r' ×ˢ Ioc s' 0 ⊆
      euclideanBall (0 : Vec d) 1 ×ˢ Ioc s 0 :=
    prod_mono ((euclideanBall_mono hr' hr'ρ.le).trans hρU) (Ioc_subset_Ioc hss'.le le_rfl)
  have hL : ∫⁻ z in euclideanBall (0 : Vec d) r' ×ˢ Ioc s' 0,
      ENNReal.ofReal ((u.toFun z + ε) ^ (r * χ)) ≤ Cd * M ^ (2 / (d : ℝ)) * M := by
    refine le_trans (le_of_eq ?_) (le_trans (lintegral_mono_set hQ'sub) hmain')
    refine setLIntegral_congr_fun ((measurableSet_euclideanBall _ _).prod measurableSet_Ioc)
      fun z hz => ?_
    have : η z = 1 := h1 z ⟨hz.1, hz.2.1.le⟩
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
        exact (le_div_iff₀ hg2).1 hZ
    _ ≤ C₀ := le_max_right _ _

end PDE.Parabolic.WeakHarnack
