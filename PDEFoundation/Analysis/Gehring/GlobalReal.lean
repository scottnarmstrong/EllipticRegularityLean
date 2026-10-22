module

public import PDEFoundation.Analysis.Gehring.TruncHolder

/-!
# Real-variable absorption and monotone convergence for the global estimate
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- Real absorption: `a ≤ a/8 + K a^e` with `0 ≤ e < 1` gives `a^(1-e) ≤ (8/7) K`. -/
theorem absorb_real {a K e : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) (he1 : e < 1)
    (h : a ≤ a / 8 + K * a ^ e) : a ^ (1 - e) ≤ 8 / 7 * K := by
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith)]; positivity
  · have h1 : 7 / 8 * a ≤ K * a ^ e := by linarith
    have hae : 0 < a ^ e := Real.rpow_pos_of_pos hpos _
    rw [Real.rpow_sub hpos, Real.rpow_one, div_le_iff₀ hae]
    nlinarith

theorem gehringN_le (σ : ℝ) (hσ : σ = 2 ∨ σ = 4) (d : ℕ) : gehringN σ d ≤ gehringN 4 d := by
  unfold gehringN
  have h : σ + 1 ≤ 4 + 1 := by
    rcases hσ with h | h
    · rw [h]; norm_num
    · rw [h]
  have h0 : 0 ≤ σ + 1 := by
    rcases hσ with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  gcongr

theorem gehringN_pos (σ : ℝ) (hσ : σ = 2 ∨ σ = 4) (d : ℕ) : 0 < gehringN σ d := by
  unfold gehringN
  have h0 : 0 < σ + 1 := by
    rcases hσ with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  positivity

/-- Monotone convergence: a uniform bound on the truncated moments bounds `∫ g^{1+ε}`. -/
theorem lintegral_rpow_le_of_truncMoment {g : Vec d → ℝ}
    (hgm : Measurable g) {ε : ℝ} (hε : 0 < ε) {M : ℝ≥0∞}
    (hM : ∀ n : ℕ, truncMoment g ((n : ℝ) + 1) ε ≤ M) :
    ∫⁻ x, ENNReal.ofReal (g x) ^ (1 + ε) ≤ M := by
  set f : ℕ → Vec d → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal ((n : ℝ) + 1))) ^ ε
    with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (ENNReal.measurable_ofReal.comp hgm).mul
      (((ENNReal.measurable_ofReal.comp hgm).min measurable_const).pow_const ε)
  have hmono : ∀ x, Monotone fun n => f n x := by
    intro x n m hnm
    have : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have h2 : min (ENNReal.ofReal (g x)) (ENNReal.ofReal ((n : ℝ) + 1)) ≤
        min (ENNReal.ofReal (g x)) (ENNReal.ofReal ((m : ℝ) + 1)) :=
      min_le_min le_rfl (ENNReal.ofReal_le_ofReal this)
    exact mul_le_mul_right (ENNReal.rpow_le_rpow h2 hε.le) _
  have hpt : ∀ x, ENNReal.ofReal (g x) ^ (1 + ε) ≤ ⨆ n, f n x := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge (g x)
    refine le_trans ?_ (le_iSup _ n)
    have hmin : min (ENNReal.ofReal (g x)) (ENNReal.ofReal ((n : ℝ) + 1)) =
        ENNReal.ofReal (g x) :=
      min_eq_left (ENNReal.ofReal_le_ofReal (by linarith))
    simp only [hf, hmin]
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one hε.le, ENNReal.rpow_one]
  calc ∫⁻ x, ENNReal.ofReal (g x) ^ (1 + ε) ≤ ∫⁻ x, ⨆ n, f n x := lintegral_mono hpt
    _ = ⨆ n, ∫⁻ x, f n x :=
        lintegral_iSup' (fun n => (hfm n).aemeasurable) (Filter.Eventually.of_forall hmono)
    _ ≤ M := iSup_le fun n => hM n

end PDE.Gehring
