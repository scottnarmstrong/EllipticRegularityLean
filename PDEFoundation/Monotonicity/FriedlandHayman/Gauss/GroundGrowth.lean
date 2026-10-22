module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.GroundSub
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Friedland--Hayman: polynomial growth of the ground state

Let `ψ = ouSol β τ` with `β = gaussBeta τ` and `q = ψ'/ψ`.  Since `0 ≤ q ≤ s/2` for large `s`
(`GroundSub`), the function `D = s q - 2β` satisfies `(D e^{-s²/4})' ≥ 0`; if `D` were positive
somewhere, `D ≥ ε e^{s²/4}` would contradict `D ≤ s²/2`.  Hence `s ψ' ≤ 2β ψ`, and
`ψ s^{-2β}` is nonincreasing.  This gives `ψ ≤ C s^{2β}` and `0 ≤ ψ' ≤ C s^{2β}` for large `s`
(real exponent, i.e. `Real.rpow`).
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

section Riccati

variable {β τ : ℝ}

/-- The logarithmic derivative `q = ψ'/ψ` of the ground state. -/
def groundQ (β τ s : ℝ) : ℝ := ouSolDeriv β τ s / ouSol β τ s

theorem hasDerivAt_groundQ {s : ℝ} (hψ : 0 < ouSol β τ s) :
    HasDerivAt (groundQ β τ) (s * groundQ β τ s - β - groundQ β τ s ^ 2) s := by
  have h := (hasDerivAt_ouSolDeriv β τ s).div (hasDerivAt_ouSol β τ s) hψ.ne'
  have e : groundQ β τ = ouSolDeriv β τ / ouSol β τ := rfl
  rw [e]
  convert h using 1
  have := hψ.ne'
  simp only [Pi.div_apply]
  field_simp

/-- `D = s q - 2β`. -/
def groundD (β τ s : ℝ) : ℝ := s * groundQ β τ s - 2 * β

theorem hasDerivAt_groundD_exp {s : ℝ} (hψ : 0 < ouSol β τ s) :
    HasDerivAt (fun x => groundD β τ x * Real.exp (-(1 / 4) * x ^ 2))
      (groundQ β τ s * (1 + s ^ 2 / 2 - s * groundQ β τ s) * Real.exp (-(1 / 4) * s ^ 2)) s := by
  have hD : HasDerivAt (groundD β τ)
      (1 * groundQ β τ s + s * (s * groundQ β τ s - β - groundQ β τ s ^ 2)) s := by
    have h : HasDerivAt (fun x => x * groundQ β τ x - 2 * β)
        (1 * groundQ β τ s + s * (s * groundQ β τ s - β - groundQ β τ s ^ 2)) s :=
      ((hasDerivAt_id' s).mul (hasDerivAt_groundQ hψ)).sub_const _
    exact h
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-(1 / 4) * x ^ 2))
      (Real.exp (-(1 / 4) * s ^ 2) * (-(1 / 4) * (2 * s))) s := by
    have := ((hasDerivAt_pow 2 s).const_mul (-(1 / 4) : ℝ)).exp
    convert this using 1
    simp
  convert hD.mul hE using 1
  unfold groundD
  ring

end Riccati


section Growth

theorem exp_quarter_sq_ge (s : ℝ) : s ^ 4 / 32 ≤ Real.exp (s ^ 2 / 4) := by
  have := Real.quadratic_le_exp_of_nonneg (x := s ^ 2 / 4) (by positivity)
  linarith [sq_nonneg s]

theorem groundD_nonpos {τ L : ℝ} (hL : max τ 0 < L) (hLsq : 4 * gaussBeta τ + 2 ≤ L ^ 2) :
    ∀ s, L ≤ s → groundD (gaussBeta τ) τ s ≤ 0 := by
  set β := gaussBeta τ with hβ
  have hadm : OUAdmissible τ β := ouAdmissible_gaussBeta τ
  have hβ0 : 0 ≤ β := hadm.1
  have hτL : τ < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hL0 : 0 < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hψ : ∀ s, L ≤ s → 0 < ouSol β τ s := fun s hs => hadm.2 s (lt_of_lt_of_le hτL hs)
  have hq0 : ∀ s, L ≤ s → 0 ≤ groundQ β τ s := fun s hs =>
    div_nonneg (ouSolDeriv_nonneg hβ0 hadm.2 s (lt_of_lt_of_le hL hs)) (hψ s hs).le
  have hqle : ∀ s, L ≤ s → groundQ β τ s ≤ s / 2 := by
    intro s hs
    have hs0 : 0 ≤ s := hL0.le.trans hs
    have hs2 : 4 * β + 2 ≤ s ^ 2 := by nlinarith
    have hu := ouU_gaussBeta_neg (lt_of_lt_of_le hτL hs) hs0 hs2
    unfold ouU at hu
    unfold groundQ
    rw [div_le_iff₀ (hψ s hs)]
    linarith
  have hmono : MonotoneOn (fun x => groundD β τ x * Real.exp (-(1 / 4) * x ^ 2)) (Ici L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici L)
      (fun x hx => (hasDerivAt_groundD_exp (hψ x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hasDerivAt_groundD_exp (hψ x (interior_subset hx))).differentiableAt.differentiableWithinAt)
      ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx' : L ≤ x := hx.out.le
    rw [(hasDerivAt_groundD_exp (hψ x hx')).deriv]
    have h1 := hq0 x hx'
    have h2 := hqle x hx'
    have h3 : 0 ≤ x := hL0.le.trans hx'
    have h4 : x * groundQ β τ x ≤ x ^ 2 / 2 := by nlinarith
    have := Real.exp_pos (-(1 / 4) * x ^ 2)
    have h5 : 0 ≤ 1 + x ^ 2 / 2 - x * groundQ β τ x := by linarith
    positivity
  intro s₁ hs₁
  by_contra hpos
  push Not at hpos
  set ε : ℝ := groundD β τ s₁ * Real.exp (-(1 / 4) * s₁ ^ 2) with hε
  have hεpos : 0 < ε := mul_pos hpos (Real.exp_pos _)
  have key : ∀ s, max s₁ 1 ≤ s → ε * s ^ 2 ≤ 16 := by
    intro s hs
    have hs1 : L ≤ s := hs₁.trans ((le_max_left _ _).trans hs)
    have hs1' : 1 ≤ s := (le_max_right _ _).trans hs
    have hm := hmono hs₁ hs1 ((le_max_left _ _).trans hs)
    simp only at hm
    have hDle : groundD β τ s ≤ s ^ 2 / 2 := by
      unfold groundD
      have := hqle s hs1
      have h3 : 0 ≤ s := by linarith
      nlinarith
    have hE := Real.exp_pos (-(1 / 4) * s ^ 2)
    have hX := exp_quarter_sq_ge s
    have hXE : Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2) = 1 := by
      rw [← Real.exp_add, show s ^ 2 / 4 + -(1 / 4) * s ^ 2 = 0 by ring, Real.exp_zero]
    have h1 : ε ≤ s ^ 2 / 2 * Real.exp (-(1 / 4) * s ^ 2) :=
      hm.trans (mul_le_mul_of_nonneg_right hDle hE.le)
    have h2 : ε * Real.exp (s ^ 2 / 4) ≤ s ^ 2 / 2 := by
      calc ε * Real.exp (s ^ 2 / 4) ≤ (s ^ 2 / 2 * Real.exp (-(1 / 4) * s ^ 2))
            * Real.exp (s ^ 2 / 4) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = s ^ 2 / 2 := by
            calc _ = s ^ 2 / 2 * (Real.exp (s ^ 2 / 4) * Real.exp (-(1 / 4) * s ^ 2)) := by ring
              _ = _ := by rw [hXE, mul_one]
    have h3 : ε * (s ^ 4 / 32) ≤ s ^ 2 / 2 :=
      (mul_le_mul_of_nonneg_left hX hεpos.le).trans h2
    have hs2 : 0 < s ^ 2 := by positivity
    have : ε * s ^ 2 * s ^ 2 ≤ 16 * s ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hs2
  have hs := key (max s₁ 1 + 16 / ε) (by
    have : 0 ≤ 16 / ε := by positivity
    linarith)
  have hsge : 1 ≤ max s₁ 1 + 16 / ε := by
    have : 0 ≤ 16 / ε := by positivity
    linarith [le_max_right s₁ 1]
  set t : ℝ := max s₁ 1 + 16 / ε with ht
  have h16 : ε * (16 / ε) = 16 := by field_simp
  have htt : t ≤ t ^ 2 := by nlinarith
  have hge : ε * t ≤ ε * t ^ 2 := mul_le_mul_of_nonneg_left htt hεpos.le
  have hm1 : 1 ≤ max s₁ 1 := le_max_right s₁ 1
  have : ε * t = ε * max s₁ 1 + 16 := by rw [ht]; linarith [h16]
  nlinarith

end Growth

end

end PDE.FHLane
