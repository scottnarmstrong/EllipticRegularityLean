module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.GroundPos

/-!
# Friedland--Hayman: forward invariance of `{y' ≥ (s/2) y}`

For `u = y' - (s/2) y` with `y = ouSol c τ`, the function `u e^{-s²/4}` has derivative
`(s²/4 - c - 1/2) y e^{-s²/4}`.  Hence, once `s² ≥ 4c + 2`, positivity of `y` together with
`u ≥ 0` at one point propagates to all later points.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

/-- `u = y' - (s/2) y`. -/
def ouU (c τ s : ℝ) : ℝ := ouSolDeriv c τ s - s / 2 * ouSol c τ s

theorem hasDerivAt_ouU_exp (c τ s : ℝ) :
    HasDerivAt (fun x => ouU c τ x * Real.exp (-(1 / 4) * x ^ 2))
      ((s ^ 2 / 4 - c - 1 / 2) * ouSol c τ s * Real.exp (-(1 / 4) * s ^ 2)) s := by
  have hu : HasDerivAt (ouU c τ)
      (s / 2 * ouSolDeriv c τ s - (c + 1 / 2) * ouSol c τ s) s := by
    have h : HasDerivAt (fun x => ouSolDeriv c τ x - x / 2 * ouSol c τ x)
        (s * ouSolDeriv c τ s - c * ouSol c τ s
          - (1 / 2 * ouSol c τ s + s / 2 * ouSolDeriv c τ s)) s :=
      (hasDerivAt_ouSolDeriv c τ s).sub
        (((hasDerivAt_id' s).div_const 2).mul (hasDerivAt_ouSol c τ s))
    have e : ouU c τ = fun x => ouSolDeriv c τ x - x / 2 * ouSol c τ x := rfl
    rw [e]
    convert h using 1
    ring
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-(1 / 4) * x ^ 2))
      (Real.exp (-(1 / 4) * s ^ 2) * (-(1 / 4) * (2 * s))) s := by
    have := ((hasDerivAt_pow 2 s).const_mul (-(1 / 4) : ℝ)).exp
    convert this using 1
    simp
  convert hu.mul hE using 1
  unfold ouU
  ring

theorem ouU_exp_monotoneOn {c τ L M : ℝ} (hL0 : 0 ≤ L) (hL : 4 * c + 2 ≤ L ^ 2) (hLM : L ≤ M)
    (hpos : ∀ t, L ≤ t → t ≤ M → 0 < ouSol c τ t) :
    ouU c τ L * Real.exp (-(1 / 4) * L ^ 2) ≤ ouU c τ M * Real.exp (-(1 / 4) * M ^ 2) := by
  have hmono : MonotoneOn (fun x => ouU c τ x * Real.exp (-(1 / 4) * x ^ 2)) (Icc L M) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x _ => (hasDerivAt_ouU_exp c τ x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_ouU_exp c τ x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_ouU_exp c τ x).deriv]
    have h1 : 4 * c + 2 ≤ x ^ 2 := by nlinarith [hx.1]
    have := hpos x hx.1.le hx.2.le
    have := Real.exp_pos (-(1 / 4) * x ^ 2)
    have h2 : 0 ≤ x ^ 2 / 4 - c - 1 / 2 := by linarith
    positivity
  exact hmono ⟨le_rfl, hLM⟩ ⟨hLM, le_rfl⟩ hLM

theorem ouU_nonneg_of_pos {c τ L M : ℝ} (hL0 : 0 ≤ L) (hL : 4 * c + 2 ≤ L ^ 2) (hLM : L ≤ M)
    (hpos : ∀ t, L ≤ t → t ≤ M → 0 < ouSol c τ t) (hu : 0 ≤ ouU c τ L) : 0 ≤ ouU c τ M := by
  have := ouU_exp_monotoneOn hL0 hL hLM hpos
  have h1 : 0 ≤ ouU c τ L * Real.exp (-(1 / 4) * L ^ 2) := mul_nonneg hu (Real.exp_pos _).le
  have h2 := Real.exp_pos (-(1 / 4) * M ^ 2)
  by_contra hneg
  push Not at hneg
  nlinarith

/-- Forward invariance of `{y > 0, y' ≥ (s/2) y}`. -/
theorem ouSol_pos_forward {c τ L : ℝ} (hL0 : 0 ≤ L) (hL : 4 * c + 2 ≤ L ^ 2)
    (hφ : 0 < ouSol c τ L) (hu : 0 ≤ ouU c τ L) : ∀ s, L ≤ s → 0 < ouSol c τ s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s₀, hs₀, hs₀'⟩ := hcon
  set Z : Set ℝ := {s | L ≤ s ∧ ouSol c τ s ≤ 0} with hZ
  have hcontφ : Continuous (ouSol c τ) := (continuous_ouSol_uncurry τ).comp
    (continuous_const.prodMk continuous_id)
  have hZclosed : IsClosed Z :=
    (isClosed_Ici (a := L)).inter (isClosed_le hcontφ continuous_const)
  have hZne : Z.Nonempty := ⟨s₀, hs₀, hs₀'⟩
  have hZbdd : BddBelow Z := ⟨L, fun s hs => hs.1⟩
  have hmem := hZclosed.csInf_mem hZne hZbdd
  set s₁ := sInf Z with hs₁
  have hLs₁ : L ≤ s₁ := hmem.1
  have hs₁pos : L < s₁ := by
    refine lt_of_le_of_ne hLs₁ fun h => ?_
    have := hmem.2
    rw [← h] at this
    linarith
  have hbefore : ∀ t, L ≤ t → t < s₁ → 0 < ouSol c τ t := by
    intro t ht1 ht2
    by_contra hle
    push Not at hle
    have : s₁ ≤ t := csInf_le hZbdd ⟨ht1, hle⟩
    linarith
  have hu_before : ∀ t, L ≤ t → t < s₁ → 0 ≤ ouU c τ t := fun t ht1 ht2 =>
    ouU_nonneg_of_pos hL0 hL ht1 (fun r hr1 hr2 => hbefore r hr1 (lt_of_le_of_lt hr2 ht2)) hu
  have hmono : MonotoneOn (ouSol c τ) (Icc L s₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x _ => (hasDerivAt_ouSol c τ x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_ouSol c τ x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_ouSol c τ x).deriv]
    have h1 := hu_before x hx.1.le hx.2
    have h2 := hbefore x hx.1.le hx.2
    have h3 : 0 ≤ x := hL0.trans hx.1.le
    unfold ouU at h1
    nlinarith [mul_nonneg h3 h2.le]
  have := hmono ⟨le_rfl, hLs₁⟩ ⟨hLs₁, le_rfl⟩ hLs₁
  have := hmem.2
  linarith

/-- Strict increase of `u e^{-s²/4}` on `[L, L+1]`. -/
theorem ouU_succ_pos {c τ L : ℝ} (hL0 : 0 ≤ L) (hL : 4 * c + 2 ≤ L ^ 2)
    (hpos : ∀ t, L ≤ t → t ≤ L + 1 → 0 < ouSol c τ t) (hu : 0 ≤ ouU c τ L) :
    0 < ouU c τ (L + 1) := by
  have hmono : StrictMonoOn (fun x => ouU c τ x * Real.exp (-(1 / 4) * x ^ 2)) (Icc L (L + 1)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ => (hasDerivAt_ouU_exp c τ x).continuousAt.continuousWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_ouU_exp c τ x).deriv]
    have h1 : 4 * c + 2 < x ^ 2 := by nlinarith [hx.1]
    have := hpos x hx.1.le hx.2.le
    have := Real.exp_pos (-(1 / 4) * x ^ 2)
    have h2 : 0 < x ^ 2 / 4 - c - 1 / 2 := by linarith
    positivity
  have h := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have h1 : 0 ≤ ouU c τ L * Real.exp (-(1 / 4) * L ^ 2) := mul_nonneg hu (Real.exp_pos _).le
  have h2 := Real.exp_pos (-(1 / 4) * (L + 1) ^ 2)
  by_contra hneg
  push Not at hneg
  simp only at h
  nlinarith

end

end PDE.FHLane
