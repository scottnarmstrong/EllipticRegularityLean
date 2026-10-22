module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.BartaLimit

/-!
# Friedland--Hayman: the lower boundary term of Barta's inequality

For a positive solution `φ = ouSol c τ` on `(τ, ∞)` and a test function `g`, the quantity
`F a = (φ'/φ) g² w` tends to `0` as `a ↓ τ`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

theorem gaussW_lower {τ x : ℝ} (hx1 : τ ≤ x) (hx2 : x ≤ τ + 1) :
    gaussW (|τ| + 1) ≤ gaussW x := by
  unfold gaussW
  apply Real.exp_le_exp.mpr
  have h1 : |x| ≤ |τ| + 1 := by
    rw [abs_le]
    constructor <;> cases abs_cases τ <;> linarith
  have : x ^ 2 ≤ (|τ| + 1) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  linarith

theorem bartaF_tendsto_zero {c τ : ℝ} {g g' : ℝ → ℝ} (hpos : ∀ s, τ < s → 0 < ouSol c τ s)
    (hg : GaussTest τ g g') : Tendsto (bartaF c τ g) (𝓝[>] τ) (𝓝 0) := by
  obtain ⟨δ, hδ, hδ1, hnear⟩ := ouSol_near c τ
  set m : ℝ := gaussW (|τ| + 1) with hm
  have hmpos : 0 < m := gaussW_pos _
  set J : ℝ → ℝ := fun a => ∫ x in Ioc τ a, g' x ^ 2 * gaussW x with hJ
  have hJ0 : Tendsto J (𝓝[>] τ) (𝓝 0) := tendsto_setIntegral_Ioc_zero hg.int_dsq
  have hbound : ∀ a, τ < a → a ≤ τ + δ → 0 ≤ bartaF c τ g a ∧
      bartaF c τ g a ≤ (4 / m) * J a := by
    intro a h1 h2
    obtain ⟨hφa, hD1, hD2⟩ := hnear a h1 h2
    have hsub : Ioc τ a ⊆ Ioi τ := fun x hx => hx.1
    have hsq_cont : ContinuousOn (fun x => g' x ^ 2) (Ioc τ a) :=
      (hg.cont'.mono hsub).pow 2
    have hint_w : IntegrableOn (fun x => g' x ^ 2 * gaussW x) (Ioc τ a) :=
      hg.int_dsq.mono_set hsub
    have hint_sq : IntegrableOn (fun x => g' x ^ 2) (Ioc τ a) := by
      refine (hint_w.const_mul (1 / m)).mono' (hsq_cont.aestronglyMeasurable measurableSet_Ioc) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
      have hw := gaussW_lower hx.1.le (by linarith [hx.2])
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← hm] at hw
      have : g' x ^ 2 * m ≤ g' x ^ 2 * gaussW x := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hmpos]
      linarith
    have hint_one : IntegrableOn g' (Ioc τ a) := by
      refine (integrableOn_const (C := (1 : ℝ)) (by simp) |>.add hint_sq).mono' ((hg.cont'.mono hsub).aestronglyMeasurable measurableSet_Ioc) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x _ => ?_)
      rw [Real.norm_eq_abs]
      simp only [Pi.add_apply]
      nlinarith [abs_nonneg (g' x), sq_abs (g' x), sq_nonneg (|g' x| - 1)]
    have hcs := sq_le_mul_integral_sq h1 hg.cont.continuousOn (hg.eq_zero τ le_rfl)
      (fun x hx => hg.hasDeriv x hx.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1.le).mpr hint_one)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1.le).mpr hint_sq)
    rw [intervalIntegral.integral_of_le h1.le] at hcs
    have hI : ∫ x in Ioc τ a, g' x ^ 2 ≤ (1 / m) * J a := by
      rw [hJ]
      simp only
      rw [← integral_const_mul]
      refine setIntegral_mono_on hint_sq (hint_w.const_mul _) measurableSet_Ioc ?_
      intro x hx
      have hw := gaussW_lower hx.1.le (by linarith [hx.2])
      rw [← hm] at hw
      have : g' x ^ 2 * m ≤ g' x ^ 2 * gaussW x := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hmpos]
      linarith
    have hτa : 0 < a - τ := sub_pos.mpr h1
    have hφpos : 0 < ouSol c τ a := hpos a h1
    have hp0 : 0 ≤ ouSolDeriv c τ a / ouSol c τ a := div_nonneg (by linarith) hφpos.le
    have hp4 : ouSolDeriv c τ a / ouSol c τ a ≤ 4 / (a - τ) := by
      have : ouSolDeriv c τ a / ouSol c τ a ≤ 2 / ((a - τ) / 2) :=
        div_le_div₀ (by norm_num) hD2 (by positivity) hφa
      calc _ ≤ _ := this
        _ = 4 / (a - τ) := by field_simp; ring
    unfold bartaF
    constructor
    · exact mul_nonneg (mul_nonneg hp0 (sq_nonneg _)) (gaussW_pos _).le
    · have hw1 := gaussW_le_one a
      have hgsq : 0 ≤ g a ^ 2 := sq_nonneg _
      calc ouSolDeriv c τ a / ouSol c τ a * g a ^ 2 * gaussW a
          ≤ ouSolDeriv c τ a / ouSol c τ a * g a ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hw1 (mul_nonneg hp0 hgsq)
        _ ≤ 4 / (a - τ) * g a ^ 2 := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right hp4 hgsq
        _ ≤ 4 / (a - τ) * ((a - τ) * ∫ x in Ioc τ a, g' x ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = 4 * ∫ x in Ioc τ a, g' x ^ 2 := by field_simp
        _ ≤ 4 * ((1 / m) * J a) := by gcongr
        _ = 4 / m * J a := by ring
  have hev : ∀ᶠ a in 𝓝[>] τ, τ < a ∧ a ≤ τ + δ :=
    Ioc_mem_nhdsGT (by linarith : τ < τ + δ)
  refine squeeze_zero' (Eventually.mono hev fun a ha => (hbound a ha.1 ha.2).1)
    (Eventually.mono hev fun a ha => (hbound a ha.1 ha.2).2) ?_
  simpa using hJ0.const_mul (4 / m)

end

end PDE.FHLane
