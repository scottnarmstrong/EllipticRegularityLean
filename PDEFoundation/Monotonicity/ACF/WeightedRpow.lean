module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The regularized weight `(s + ε²)^{-κ}` and its first two derivatives

Real-variable calculus for `Q_ε(s) = (s + ε²)^{-κ}` used for the weights `g_ε(|x|) = Q_ε(|x|²)`
with `κ = (d-2)/2`: derivative formulas and the sign identity
`2 d Q_ε' + 4 s Q_ε'' = -2 d κ ε² (s + ε²)^{-κ-2} ≤ 0` when `d = 2 κ + 2`.
-/

@[expose] public section

namespace PDE

noncomputable section

/-- `Q_ε(s) = (s + ε²)^{-κ}`. -/
def acfQ (κ ε s : ℝ) : ℝ := (s + ε ^ 2) ^ (-κ)

/-- First derivative of `acfQ`. -/
def acfQ1 (κ ε s : ℝ) : ℝ := -κ * (s + ε ^ 2) ^ (-κ - 1)

/-- Second derivative of `acfQ`. -/
def acfQ2 (κ ε s : ℝ) : ℝ := κ * (κ + 1) * (s + ε ^ 2) ^ (-κ - 2)

theorem hasDerivAt_acfQ {κ ε s : ℝ} (h : 0 < s + ε ^ 2) :
    HasDerivAt (acfQ κ ε) (acfQ1 κ ε s) s := by
  have := ((hasDerivAt_id s).add_const (ε ^ 2)).rpow_const (p := -κ) (Or.inl h.ne')
  refine this.congr_deriv ?_
  simp [acfQ1]

theorem hasDerivAt_acfQ1 {κ ε s : ℝ} (h : 0 < s + ε ^ 2) :
    HasDerivAt (acfQ1 κ ε) (acfQ2 κ ε s) s := by
  have := (((hasDerivAt_id s).add_const (ε ^ 2)).rpow_const (p := -κ - 1)
    (Or.inl h.ne')).const_mul (-κ)
  refine this.congr_deriv ?_
  simp only [acfQ2, id]
  ring_nf

theorem acfQ_nonneg {κ ε s : ℝ} (h : 0 ≤ s + ε ^ 2) : 0 ≤ acfQ κ ε s :=
  Real.rpow_nonneg h _

theorem acfQ_pos {κ ε s : ℝ} (h : 0 < s + ε ^ 2) : 0 < acfQ κ ε s :=
  Real.rpow_pos_of_pos h _

theorem acfQ1_mul_self_eq {κ ε s : ℝ} (h : 0 < s + ε ^ 2) :
    (s + ε ^ 2) * acfQ1 κ ε s = -κ * acfQ κ ε s := by
  unfold acfQ1 acfQ
  rw [Real.rpow_sub_one h.ne']
  field_simp

/-- The sign identity for the regularized weight. -/
theorem acf_laplace_Q {κ ε s : ℝ} {d : ℝ} (hd : d = 2 * κ + 2) (h : 0 < s + ε ^ 2) :
    2 * d * acfQ1 κ ε s + 4 * s * acfQ2 κ ε s =
      -(2 * d * κ * ε ^ 2) * (s + ε ^ 2) ^ (-κ - 2) := by
  have e1 : (s + ε ^ 2) ^ (-κ - 1) = (s + ε ^ 2) ^ (-κ - 2) * (s + ε ^ 2) := by
    have := Real.rpow_add h (-κ - 2) 1
    rw [Real.rpow_one] at this
    rw [← this]; ring_nf
  unfold acfQ1 acfQ2
  rw [e1, hd]
  ring

theorem acf_laplace_Q_nonpos {κ ε s : ℝ} {d : ℝ} (hd : d = 2 * κ + 2) (hκ : 0 ≤ κ)
    (h : 0 < s + ε ^ 2) : 2 * d * acfQ1 κ ε s + 4 * s * acfQ2 κ ε s ≤ 0 := by
  rw [acf_laplace_Q hd h]
  have : 0 ≤ (s + ε ^ 2) ^ (-κ - 2) := Real.rpow_nonneg h.le _
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have : 0 ≤ 2 * d * κ * ε ^ 2 * (s + ε ^ 2) ^ (-κ - 2) := by positivity
  linarith

end

end PDE
