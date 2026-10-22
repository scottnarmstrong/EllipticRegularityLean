module

public import PDEFoundation.Monotonicity.FriedlandHayman.Gauss.Solution
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Friedland--Hayman: Sturm-type facts for the Hermite equation

Positivity of `ouSol c τ₁` on `(τ₁, ∞)` propagates to `ouSol c τ₂` on `(τ₂, ∞)` for `τ₁ ≤ τ₂`
(Sturm separation, via the Wronskian and the monotone quotient `ouSol c τ₂ / ouSol c τ₁`), and
for `c ≥ 0` a positive solution has nonnegative derivative.
-/

@[expose] public section

open Set

namespace PDE.FHLane

noncomputable section

/-- Sturm separation: positivity on `(τ₁, ∞)` propagates to later starting points. -/
theorem ouSol_pos_of_le {c τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) (hpos : ∀ s, τ₁ < s → 0 < ouSol c τ₁ s) :
    ∀ s, τ₂ < s → 0 < ouSol c τ₂ s := by
  rcases h.eq_or_lt with rfl | hlt
  · exact hpos
  have hd := fun x => hasDerivAt_ouWronskian (c₁ := c) (c₂ := c)
    (hasDerivAt_ouSol c τ₁) (hasDerivAt_ouSolDeriv c τ₁) (hasDerivAt_ouSol c τ₂)
    (hasDerivAt_ouSolDeriv c τ₂) x
  have hconst := fun s => is_const_of_deriv_eq_zero (f := fun s =>
      (ouSolDeriv c τ₂ s * ouSol c τ₁ s - ouSol c τ₂ s * ouSolDeriv c τ₁ s)
        * Real.exp (-(s ^ 2) / 2))
    (fun x => (hd x).differentiableAt) (fun x => by rw [(hd x).deriv]; ring) s τ₂
  have hW : ∀ s, 0 < ouSolDeriv c τ₂ s * ouSol c τ₁ s - ouSol c τ₂ s * ouSolDeriv c τ₁ s := by
    intro s
    have h1 := hconst s
    simp only [ouSol_self, ouSolDeriv_self, zero_mul, sub_zero, one_mul] at h1
    have h2 : 0 < ouSol c τ₁ τ₂ * Real.exp (-(τ₂ ^ 2) / 2) :=
      mul_pos (hpos τ₂ hlt) (Real.exp_pos _)
    have h3 : 0 < (ouSolDeriv c τ₂ s * ouSol c τ₁ s - ouSol c τ₂ s * ouSolDeriv c τ₁ s)
        * Real.exp (-(s ^ 2) / 2) := by rw [h1]; exact h2
    exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp h3
  have hφ1 : ∀ s, τ₂ ≤ s → 0 < ouSol c τ₁ s := fun s hs => hpos s (hlt.trans_le hs)
  have hψ : ∀ s, τ₂ ≤ s → HasDerivAt (fun s => ouSol c τ₂ s / ouSol c τ₁ s)
      ((ouSolDeriv c τ₂ s * ouSol c τ₁ s - ouSol c τ₂ s * ouSolDeriv c τ₁ s)
        / ouSol c τ₁ s ^ 2) s := fun s hs =>
    (hasDerivAt_ouSol c τ₂ s).div (hasDerivAt_ouSol c τ₁ s) (hφ1 s hs).ne'
  have hmono : StrictMonoOn (fun s => ouSol c τ₂ s / ouSol c τ₁ s) (Ici τ₂) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici τ₂) (fun s hs => (hψ s hs).continuousAt.continuousWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    rw [(hψ s (le_of_lt hs)).deriv]
    exact div_pos (hW s) (pow_pos (hφ1 s hs.le) 2)
  intro s hs
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs
  simp only [ouSol_self, zero_div] at this
  exact (div_pos_iff_of_pos_right (hφ1 s hs.le)).mp this

/-- For `c ≥ 0` a solution positive on `(τ, ∞)` is nondecreasing on `(max τ 0, ∞)`. -/
theorem ouSolDeriv_nonneg {c τ : ℝ} (hc : 0 ≤ c) (hpos : ∀ s, τ < s → 0 < ouSol c τ s) :
    ∀ s, max τ 0 < s → 0 ≤ ouSolDeriv c τ s := by
  intro s₀ hs₀
  have hτ : τ < s₀ := lt_of_le_of_lt (le_max_left _ _) hs₀
  by_contra hneg
  push Not at hneg
  have hg : ∀ x, HasDerivAt (fun x => ouSolDeriv c τ x * Real.exp (-(x ^ 2) / 2))
      (-(c * ouSol c τ x) * Real.exp (-(x ^ 2) / 2)) x := by
    intro x
    have hE : HasDerivAt (fun s : ℝ => Real.exp (-(s ^ 2) / 2))
        (Real.exp (-(x ^ 2) / 2) * (-x)) x := by
      have h : HasDerivAt (fun s : ℝ => -(s ^ 2) / 2) (-x) x := by
        have := ((hasDerivAt_pow 2 x).neg).div_const 2
        convert this using 1
        simp
        ring
      exact h.exp
    convert (hasDerivAt_ouSolDeriv c τ x).mul hE using 1
    ring
  have hanti : AntitoneOn (fun x => ouSolDeriv c τ x * Real.exp (-(x ^ 2) / 2)) (Ioi τ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi τ)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ioi] at hx
    rw [(hg x).deriv]
    have := hpos x hx
    have := Real.exp_pos (-(x ^ 2) / 2)
    nlinarith [mul_nonneg hc this.le, mul_nonneg (mul_nonneg hc (hpos x hx).le) this.le]
  set δ : ℝ := -(ouSolDeriv c τ s₀ * Real.exp (-(s₀ ^ 2) / 2)) with hδ
  have hδpos : 0 < δ := by
    have := Real.exp_pos (-(s₀ ^ 2) / 2)
    rw [hδ]; nlinarith
  have hbound : ∀ s, s₀ ≤ s → ouSolDeriv c τ s ≤ -δ := by
    intro s hs
    have h1 := hanti (Set.mem_Ioi.mpr hτ) (Set.mem_Ioi.mpr (hτ.trans_le hs)) hs
    simp only at h1
    have hexp : 1 ≤ Real.exp ((s ^ 2) / 2) := Real.one_le_exp (by positivity)
    have hmul : Real.exp (-(s ^ 2) / 2) * Real.exp ((s ^ 2) / 2) = 1 := by
      rw [← Real.exp_add, show -(s ^ 2) / 2 + s ^ 2 / 2 = 0 by ring, Real.exp_zero]
    have : ouSolDeriv c τ s = (ouSolDeriv c τ s * Real.exp (-(s ^ 2) / 2)) * Real.exp ((s ^ 2) / 2) := by
      rw [mul_assoc, hmul, mul_one]
    rw [this]
    have h2 : (ouSolDeriv c τ s * Real.exp (-(s ^ 2) / 2)) ≤ -δ := by rw [hδ]; linarith
    nlinarith
  have hd2 : ∀ x, HasDerivAt (fun x => ouSol c τ x + δ * x) (ouSolDeriv c τ x + δ) x := by
    intro x
    have := (hasDerivAt_ouSol c τ x).add ((hasDerivAt_id x).const_mul δ)
    convert this using 1 <;> first | rfl | simp
  have hanti2 : AntitoneOn (fun x => ouSol c τ x + δ * x) (Ici s₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici s₀)
      (fun x _ => (hd2 x).continuousAt.continuousWithinAt)
      (fun x _ => (hd2 x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd2 x).deriv]
    have := hbound x hx.le
    linarith
  set s₁ : ℝ := s₀ + ouSol c τ s₀ / δ + 1 with hs₁
  have hs₁' : s₀ ≤ s₁ := by
    have := hpos s₀ hτ
    have : 0 ≤ ouSol c τ s₀ / δ := by positivity
    rw [hs₁]; linarith
  have h := hanti2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs₁') hs₁'
  simp only at h
  have hq : δ * (ouSol c τ s₀ / δ) = ouSol c τ s₀ := by field_simp
  have hpos1 := hpos s₁ (by have := hpos s₀ hτ; have : 0 ≤ ouSol c τ s₀ / δ := by positivity
                            rw [hs₁]; linarith)
  nlinarith

end

end PDE.FHLane
