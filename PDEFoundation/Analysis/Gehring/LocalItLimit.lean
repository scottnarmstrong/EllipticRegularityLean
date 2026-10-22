module

public import PDEFoundation.Analysis.Gehring.LocalItBound

/-!
# The local `L^{1+ε}` estimate on `B_{1/2}` (Lemma 4.6, `L → ∞`)

`∫_{B_{1/2}} g^{1+ε} ≤ 4 ω m^{1+ε} + (4/3) 8^ε (2 B N_σ)^{1+ε} ∫ h^{1+ε}`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- **Local integral estimate** for measurable `g` supported in `B_1`: the iteration of
`local_step` along `ρ_j`, followed by monotone convergence in `L`. -/
theorem local_iteration (hd : 2 ≤ d) {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hgm : Measurable g) (hg : Integrable g volume)
    (hc : HasCompactSupport g) {σ A B ε : ℝ}
    (hh : MemLp h (ENNReal.ofReal (1 + ε)) volume) (hσ : σ = 2 ∨ σ = 4) (hA : 1 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (hεA : ε ≤ 1 / (8 * gehringG d * A))
    (hsupp : ∀ x, x ∉ euclideanBall (0 : Vec d) 1 → g x = 0)
    (hm : 0 < integralAverage (euclideanBall (0 : Vec d) 1) g)
    (hrh : ∀ (z : Vec d) (r : ℝ), 0 < r → centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) 1 →
      GehringRH d σ A B g h z r) :
    ∫⁻ x in euclideanBall (0 : Vec d) (1 / 2), ENNReal.ofReal (g x) ^ (1 + ε) ≤
      ENNReal.ofReal (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal *
          integralAverage (euclideanBall (0 : Vec d) 1) g ^ (1 + ε)) +
        ENNReal.ofReal (4 / 3 * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε))) *
          ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) := by
  set Bh := euclideanBall (0 : Vec d) (1 / 2) with hBh
  have hBhm : MeasurableSet Bh := (isOpen_euclideanBall _ _).measurableSet
  set Hraw := ∫⁻ x, ENNReal.ofReal (h x) ^ (1 + ε) with hHraw
  have hHfin : Hraw < ⊤ := lintegral_rpow_lt_top_of_memLp hh0 hε hh
  have hM : ∀ n : ℕ, truncMoment (Bh.indicator g) ((n : ℝ) + 1) ε ≤
      ENNReal.ofReal (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal *
          integralAverage (euclideanBall (0 : Vec d) 1) g ^ (1 + ε) +
        4 / 3 * ((8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)) * Hraw.toReal)) := by
    intro n
    rw [truncMoment_indicator hBhm hε]
    exact local_iteration_L hd hg0 hh0 hgm hg hc hh hσ hA hB hε hεA (by positivity) hsupp hm hrh
  have hlim := lintegral_rpow_le_of_truncMoment ((hgm.indicator hBhm)) hε hM
  have e1 : ∫⁻ x in Bh, ENNReal.ofReal (g x) ^ (1 + ε) =
      ∫⁻ x, ENNReal.ofReal (Bh.indicator g x) ^ (1 + ε) := by
    rw [← lintegral_indicator hBhm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Bh
    · simp [hx]
    · simp [hx, ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < 1 + ε)]
  rw [e1]
  refine hlim.trans (le_of_eq ?_)
  have hω0 : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal := ENNReal.toReal_nonneg
  have hN := gehringN_pos σ hσ d
  have h1 : 0 ≤ 4 * (volume (euclideanBall (0 : Vec d) 1)).toReal *
      integralAverage (euclideanBall (0 : Vec d) 1) g ^ (1 + ε) := by positivity
  have h2 : 0 ≤ 4 / 3 * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)) := by positivity
  rw [ENNReal.ofReal_add h1 (by positivity)]
  congr 1
  rw [show 4 / 3 * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε) * Hraw.toReal) =
    (4 / 3 * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε))) * Hraw.toReal by ring,
    ENNReal.ofReal_mul h2, ENNReal.ofReal_toReal hHfin.ne]

end PDE.Gehring
