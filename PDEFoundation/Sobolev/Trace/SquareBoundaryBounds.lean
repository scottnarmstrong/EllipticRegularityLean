module

public import PDEFoundation.Sobolev.Trace.SquareBoundaryEnergy

/-!
# Pointwise bounds from square-boundary oscillation

This module converts a squared oscillation estimate for a continuous
four-side trace into explicit upper and lower bounds relative to one fixed
boundary value.  The square root of the displayed oscillation constant
remains literal.
-/

@[expose] public section

namespace PDE

open Set

noncomputable section

namespace SquareSideTrace.HasBoundarySqOscillationLE

/-- A square-boundary oscillation estimate may be enlarged monotonically. -/
theorem mono
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r B B' : ℝ}
    {T : SquareSideTrace u g x₀ r}
    (h : T.HasBoundarySqOscillationLE B) (hBB' : B ≤ B') :
    T.HasBoundarySqOscillationLE B' := by
  intro side₁ side₂ s t hs ht
  exact (h hs ht).trans hBB'

/-- Taking square roots converts a squared boundary-oscillation estimate into
an absolute pointwise increment estimate. -/
theorem abs_sideValue_sub_sideValue_le_sqrt
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r B : ℝ}
    {T : SquareSideTrace u g x₀ r}
    (h : T.HasBoundarySqOscillationLE B) (hB : 0 ≤ B)
    {side₁ side₂ : SquareTraceSide} {s t : ℝ}
    (hs : s ∈ squareTraceSideParameterSet x₀ r side₁)
    (ht : t ∈ squareTraceSideParameterSet x₀ r side₂) :
    |T.sideValue side₁ s - T.sideValue side₂ t| ≤ Real.sqrt B := by
  have hsq := h hs ht
  nlinarith [Real.sq_sqrt hB, Real.sqrt_nonneg B,
    abs_nonneg (T.sideValue side₁ s - T.sideValue side₂ t)]

/-- Every boundary value is bounded above by any fixed boundary value plus
the square root of the squared oscillation constant. -/
theorem sideValue_le_sideValue_add_sqrt
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r B : ℝ}
    {T : SquareSideTrace u g x₀ r}
    (h : T.HasBoundarySqOscillationLE B) (hB : 0 ≤ B)
    {side₁ side₂ : SquareTraceSide} {s t : ℝ}
    (hs : s ∈ squareTraceSideParameterSet x₀ r side₁)
    (ht : t ∈ squareTraceSideParameterSet x₀ r side₂) :
    T.sideValue side₁ s ≤ T.sideValue side₂ t + Real.sqrt B := by
  have habs := h.abs_sideValue_sub_sideValue_le_sqrt hB hs ht
  have hsub := (abs_le.mp habs).2
  linarith

/-- Every boundary value is bounded below by any fixed boundary value minus
the square root of the squared oscillation constant. -/
theorem sideValue_sub_sqrt_le_sideValue
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r B : ℝ}
    {T : SquareSideTrace u g x₀ r}
    (h : T.HasBoundarySqOscillationLE B) (hB : 0 ≤ B)
    {side₁ side₂ : SquareTraceSide} {s t : ℝ}
    (hs : s ∈ squareTraceSideParameterSet x₀ r side₁)
    (ht : t ∈ squareTraceSideParameterSet x₀ r side₂) :
    T.sideValue side₂ t - Real.sqrt B ≤ T.sideValue side₁ s := by
  have habs := h.abs_sideValue_sub_sideValue_le_sqrt hB hs ht
  have hsub := (abs_le.mp habs).1
  linarith

/-- The center parameter of the right side is a valid reference point when
the square radius is nonnegative. -/
theorem sideValue_le_right_center_add_sqrt
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r B : ℝ}
    {T : SquareSideTrace u g x₀ r}
    (h : T.HasBoundarySqOscillationLE B) (hr : 0 ≤ r) (hB : 0 ≤ B) :
    ∀ (side : SquareTraceSide) (t : ℝ),
      t ∈ squareTraceSideParameterSet x₀ r side →
        T.sideValue side t ≤ T.right (x₀ 1) + Real.sqrt B := by
  intro side t ht
  have hcenter :
      x₀ 1 ∈ squareTraceSideParameterSet x₀ r .right := by
    simp only [squareTraceSideParameterSet, mem_Icc]
    constructor <;> linarith
  exact h.sideValue_le_sideValue_add_sqrt hB ht hcenter

/-- The same right-side reference value gives a uniform lower bound on all
four sides. -/
theorem right_center_sub_sqrt_le_sideValue
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r B : ℝ}
    {T : SquareSideTrace u g x₀ r}
    (h : T.HasBoundarySqOscillationLE B) (hr : 0 ≤ r) (hB : 0 ≤ B) :
    ∀ (side : SquareTraceSide) (t : ℝ),
      t ∈ squareTraceSideParameterSet x₀ r side →
        T.right (x₀ 1) - Real.sqrt B ≤ T.sideValue side t := by
  intro side t ht
  have hcenter :
      x₀ 1 ∈ squareTraceSideParameterSet x₀ r .right := by
    simp only [squareTraceSideParameterSet, mem_Icc]
    constructor <;> linarith
  exact h.sideValue_sub_sqrt_le_sideValue hB ht hcenter

end SquareSideTrace.HasBoundarySqOscillationLE

namespace SquareSideTrace

/-- A side-energy bound at an intermediate radius converts to a square-shell
boundary oscillation bound with the explicit constant `64`. -/
theorem hasBoundarySqOscillationLE_shell_of_tangential_energy_le
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2}
    {r ρ E : ℝ} (T : SquareSideTrace u g x₀ ρ)
    (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ ≤ 2 * r) (hE : 0 ≤ E)
    (henergy :
      squareSideTangentialEnergy g x₀ ρ ≤ (4 / r) * E) :
    T.HasBoundarySqOscillationLE (64 * E) := by
  apply (T.hasBoundarySqOscillationLE_actual_tangential_energy hρ).mono
  calc
    8 * ρ * squareSideTangentialEnergy g x₀ ρ ≤
        8 * ρ * ((4 / r) * E) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = 32 * (ρ / r) * E := by ring
    _ ≤ 32 * 2 * E := by
      have hratio : ρ / r ≤ 2 := (div_le_iff₀ hr).2 hρr
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by norm_num)) hE
    _ = 64 * E := by ring

end SquareSideTrace

end

end PDE
