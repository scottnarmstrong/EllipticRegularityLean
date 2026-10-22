module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Friedland--Hayman: uniqueness and Wronskian for the Hermite equation

For the Ornstein--Uhlenbeck (Hermite) equation `y'' - s y' + c y = 0`, written as the first-order
system `(y, y')' = (y', s y' - c y)`, we prove uniqueness of the Cauchy problem on all of `ℝ`
(via Grönwall on the energy `y² + y'²`, forward in time and, by the reflection `s ↦ -s` which
preserves the equation, backward in time) and the Wronskian identity for two solutions with
different parameters.
-/

@[expose] public section

open Set

namespace PDE.FHLane

noncomputable section

/-- Wronskian identity for two solutions with parameters `c₁`, `c₂`. -/
theorem hasDerivAt_ouWronskian {c₁ c₂ : ℝ} {y₁ y₁' y₂ y₂' : ℝ → ℝ}
    (h₁ : ∀ s, HasDerivAt y₁ (y₁' s) s)
    (h₁' : ∀ s, HasDerivAt y₁' (s * y₁' s - c₁ * y₁ s) s) (h₂ : ∀ s, HasDerivAt y₂ (y₂' s) s)
    (h₂' : ∀ s, HasDerivAt y₂' (s * y₂' s - c₂ * y₂ s) s) (s : ℝ) :
    HasDerivAt (fun s => (y₂' s * y₁ s - y₂ s * y₁' s) * Real.exp (-(s ^ 2) / 2))
      ((c₁ - c₂) * y₁ s * y₂ s * Real.exp (-(s ^ 2) / 2)) s := by
  have hW : HasDerivAt (fun s => y₂' s * y₁ s - y₂ s * y₁' s)
      ((s * y₂' s - c₂ * y₂ s) * y₁ s + y₂' s * y₁' s
        - (y₂' s * y₁' s + y₂ s * (s * y₁' s - c₁ * y₁ s))) s :=
    (((h₂' s).mul (h₁ s)).sub ((h₂ s).mul (h₁' s)))
  have hE : HasDerivAt (fun s : ℝ => Real.exp (-(s ^ 2) / 2))
      (Real.exp (-(s ^ 2) / 2) * (-s)) s := by
    have h : HasDerivAt (fun s : ℝ => -(s ^ 2) / 2) (-s) s := by
      have := ((hasDerivAt_pow 2 s).neg).div_const 2
      convert this using 1
      simp
      ring
    exact h.exp
  convert hW.mul hE using 1
  ring

/-- Forward uniqueness for the Hermite equation. -/
theorem ou_unique_forward {c a : ℝ} {y y' : ℝ → ℝ} (hy : ∀ s, HasDerivAt y (y' s) s)
    (hy' : ∀ s, HasDerivAt y' (s * y' s - c * y s) s) (h0 : y a = 0) (h1 : y' a = 0) :
    ∀ s, a ≤ s → y s = 0 := by
  intro b hb
  set R : ℝ := |a| + |b| with hR
  set K : ℝ := 2 * R + |1 - c| with hK
  have hu : ∀ x, HasDerivAt (fun x => y x ^ 2 + y' x ^ 2)
      (2 * y x * y' x + 2 * y' x * (x * y' x - c * y x)) x := by
    intro x
    convert ((hy x).pow 2).add ((hy' x).pow 2) using 1
    simp only [Nat.cast_ofNat]
    ring
  have key := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K) (a := a) (b := b)
    (f := fun x => y x ^ 2 + y' x ^ 2)
    (f' := fun x => 2 * y x * y' x + 2 * y' x * (x * y' x - c * y x))
    (fun x _ => (hu x).continuousAt.continuousWithinAt)
    (fun x _ => (hu x).hasDerivWithinAt) (by simp [h0, h1]) (by
      intro x hx
      have hxR : |x| ≤ R := by
        rw [hR]
        have : |x| ≤ max |a| |b| := by
          rw [abs_le]
          rcases abs_le.mp (abs_le_max_abs_abs hx.1 hx.2.le) with ⟨h, h'⟩
          exact ⟨by linarith, by linarith⟩
        have := le_max_left |a| |b|
        have := le_max_right |a| |b|
        rcases max_cases |a| |b| with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [abs_nonneg a, abs_nonneg b]
      have hnn : 0 ≤ y x ^ 2 + y' x ^ 2 := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
      have e : 2 * y x * y' x + 2 * y' x * (x * y' x - c * y x)
          = 2 * x * y' x ^ 2 + (1 - c) * (2 * (y x * y' x)) := by ring
      rw [e]
      have h1 : |2 * x * y' x ^ 2| ≤ 2 * R * y' x ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ y' x ^ 2)]
        have : |2 * x| ≤ 2 * R := by
          rw [abs_mul]; simp; linarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
      have h2 : |(1 - c) * (2 * (y x * y' x))| ≤ |1 - c| * (y x ^ 2 + y' x ^ 2) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (y x + y' x), sq_nonneg (y x - y' x)]
      have h3 : 0 ≤ |1 - c| := abs_nonneg _
      have h4 : 0 ≤ R := by rw [hR]; positivity
      calc _ ≤ |2 * x * y' x ^ 2| + |(1 - c) * (2 * (y x * y' x))| := abs_add_le _ _
        _ ≤ 2 * R * y' x ^ 2 + |1 - c| * (y x ^ 2 + y' x ^ 2) := add_le_add h1 h2
        _ ≤ K * (y x ^ 2 + y' x ^ 2) := by
          rw [hK]; nlinarith [sq_nonneg (y x), sq_nonneg (y' x)])
  have := key b ⟨hb, le_rfl⟩
  nlinarith [sq_nonneg (y b), sq_nonneg (y' b)]

/-- Uniqueness: a solution with zero Cauchy data at one point vanishes identically. -/
theorem ou_unique {c a : ℝ} {y y' : ℝ → ℝ} (hy : ∀ s, HasDerivAt y (y' s) s)
    (hy' : ∀ s, HasDerivAt y' (s * y' s - c * y s) s) (h0 : y a = 0) (h1 : y' a = 0) :
    ∀ s, y s = 0 := by
  intro s
  rcases le_total a s with h | h
  · exact ou_unique_forward hy hy' h0 h1 s h
  · -- reflection `s ↦ -s` preserves the equation
    have hz : ∀ x, HasDerivAt (fun x => y (-x)) (-y' (-x)) x := by
      intro x
      have := (hy (-x)).comp x (hasDerivAt_neg x)
      convert this using 1 <;> first | rfl | ring
    have hz' : ∀ x, HasDerivAt (fun x => -y' (-x)) (x * (-y' (-x)) - c * y (-x)) x := by
      intro x
      have := ((hy' (-x)).comp x (hasDerivAt_neg x)).neg
      convert this using 1 <;> first | rfl | ring
    have := ou_unique_forward hz hz' (a := -a) (by simpa using h0) (by simpa using h1) (-s)
      (by linarith)
    simpa using this

end

end PDE.FHLane
