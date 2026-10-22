module

public import PDEFoundation.Sobolev.Trace.Square

/-!
# Algebraic assembly of square-side oscillation bounds

The analytic trace construction supplies a one-dimensional increment estimate
on each of the four sides of a square.  This module contains the independent
finite-chain argument which turns four such estimates, joined at the corners,
into the boundary constant needed by the planar good-boundary argument.

The result is deliberately stated for scalar values along a cyclic chain.  A
later trace-facing module can instantiate each link by a portion of one side;
keeping this calculation separate makes its constant and its hypotheses easy
to check.
-/

@[expose] public section

namespace PDE

noncomputable section

/-- The square of a sum of four real numbers is at most four times the sum of
their squares.  This is the finite Cauchy--Schwarz step behind the square
boundary estimate. -/
theorem sq_sum_four_le_four_mul_sum_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Four successive square-side increments, each controlled by its own
side energy, control the endpoint increment.  Each side has length `2 * r`,
so the exact finite-chain factor is `8 * r`.

This is the only place where the four-side Cauchy--Schwarz loss occurs.  The
energies are explicit, nonnegative inputs rather than hidden constants. -/
theorem sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
    {r E₀ E₁ E₂ E₃ x₀ x₁ x₂ x₃ x₄ : ℝ}
    (h₀ : |x₀ - x₁| ^ 2 ≤ 2 * r * E₀)
    (h₁ : |x₁ - x₂| ^ 2 ≤ 2 * r * E₁)
    (h₂ : |x₂ - x₃| ^ 2 ≤ 2 * r * E₂)
    (h₃ : |x₃ - x₄| ^ 2 ≤ 2 * r * E₃) :
    |x₀ - x₄| ^ 2 ≤ 8 * r * (E₀ + E₁ + E₂ + E₃) := by
  have habs :
      |x₀ - x₄| ≤ |x₀ - x₁| + |x₁ - x₂| + |x₂ - x₃| + |x₃ - x₄| := by
    calc
      |x₀ - x₄| = |(x₀ - x₁) + (x₁ - x₂) + (x₂ - x₃) + (x₃ - x₄)| := by
        congr 1
        ring
      _ ≤ |x₀ - x₁| + |x₁ - x₂| + |x₂ - x₃| + |x₃ - x₄| := by
        calc
          |(x₀ - x₁) + (x₁ - x₂) + (x₂ - x₃) + (x₃ - x₄)| ≤
              |(x₀ - x₁) + (x₁ - x₂) + (x₂ - x₃)| + |x₃ - x₄| :=
            abs_add_le _ _
          _ ≤ (|(x₀ - x₁) + (x₁ - x₂)| + |x₂ - x₃|) + |x₃ - x₄| :=
            add_le_add (abs_add_le _ _) (le_refl _)
          _ ≤ (|x₀ - x₁| + |x₁ - x₂| + |x₂ - x₃|) + |x₃ - x₄| := by
            exact add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)
          _ = |x₀ - x₁| + |x₁ - x₂| + |x₂ - x₃| + |x₃ - x₄| := by ring
  have hsquare :
      |x₀ - x₄| ^ 2 ≤
        (|x₀ - x₁| + |x₁ - x₂| + |x₂ - x₃| + |x₃ - x₄|) ^ 2 := by
    nlinarith [abs_nonneg (x₀ - x₄), abs_nonneg (x₀ - x₁),
      abs_nonneg (x₁ - x₂), abs_nonneg (x₂ - x₃), abs_nonneg (x₃ - x₄)]
  have hsum :
      |x₀ - x₁| ^ 2 + |x₁ - x₂| ^ 2 + |x₂ - x₃| ^ 2 + |x₃ - x₄| ^ 2 ≤
        2 * r * E₀ + 2 * r * E₁ + 2 * r * E₂ + 2 * r * E₃ := by
    linarith
  calc
    |x₀ - x₄| ^ 2 ≤
        (|x₀ - x₁| + |x₁ - x₂| + |x₂ - x₃| + |x₃ - x₄|) ^ 2 := hsquare
    _ ≤ 4 * (|x₀ - x₁| ^ 2 + |x₁ - x₂| ^ 2 + |x₂ - x₃| ^ 2 + |x₃ - x₄| ^ 2) :=
      sq_sum_four_le_four_mul_sum_sq _ _ _ _
    _ ≤ 4 * (2 * r * E₀ + 2 * r * E₁ + 2 * r * E₂ + 2 * r * E₃) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 8 * r * (E₀ + E₁ + E₂ + E₃) := by ring

/-- A single side increment is bounded by the four-side boundary constant
whenever all four side energies are nonnegative.  This companion lemma covers
the same-side case, where one should not traverse a full loop and duplicate a
side energy. -/
theorem sq_abs_sub_le_eight_mul_radius_mul_sum_of_one_side
    {r E₀ E₁ E₂ E₃ x y : ℝ}
    (hr : 0 ≤ r)
    (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃)
    (hxy : |x - y| ^ 2 ≤ 2 * r * E₀) :
    |x - y| ^ 2 ≤ 8 * r * (E₀ + E₁ + E₂ + E₃) := by
  have hsum : E₀ ≤ E₀ + E₁ + E₂ + E₃ := by linarith
  have hrTwo : 0 ≤ 2 * r := by positivity
  have htotalNonneg : 0 ≤ E₀ + E₁ + E₂ + E₃ := by linarith
  calc
    |x - y| ^ 2 ≤ 2 * r * E₀ := hxy
    _ ≤ 2 * r * (E₀ + E₁ + E₂ + E₃) :=
      mul_le_mul_of_nonneg_left hsum hrTwo
    _ ≤ 8 * r * (E₀ + E₁ + E₂ + E₃) := by
      nlinarith [mul_nonneg hr htotalNonneg]

/-- The four Cartesian side labels used by a square trace.  The labels retain
the increasing-coordinate parametrization of `SquareSideTrace`; they do not
choose an orientation for a loop. -/
inductive SquareTraceSide where
  | right | top | left | bottom

/-- The parameter interval for one side of a square trace. -/
def squareTraceSideParameterSet (x₀ : Vec 2) (r : ℝ) : SquareTraceSide → Set ℝ
  | .right | .left => Set.Icc (x₀ 1 - r) (x₀ 1 + r)
  | .top | .bottom => Set.Icc (x₀ 0 - r) (x₀ 0 + r)

/-- Evaluate a square-side trace on one labelled side. -/
def SquareSideTrace.sideValue
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    (h : SquareSideTrace u g x₀ r) : SquareTraceSide → ℝ → ℝ
  | .right => h.right
  | .top => h.top
  | .left => h.left
  | .bottom => h.bottom

/-- A squared increment bound on one complete labelled side. -/
def SquareSideTrace.HasSideSqIncrementLE
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    (h : SquareSideTrace u g x₀ r) (side : SquareTraceSide) (E : ℝ) : Prop :=
  ∀ ⦃s t : ℝ⦄,
    s ∈ squareTraceSideParameterSet x₀ r side →
    t ∈ squareTraceSideParameterSet x₀ r side →
    |h.sideValue side t - h.sideValue side s| ^ 2 ≤ 2 * r * E

/-- A bound for every pair of values on the four sides of a square trace. -/
def SquareSideTrace.HasBoundarySqOscillationLE
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    (h : SquareSideTrace u g x₀ r) (B : ℝ) : Prop :=
  ∀ ⦃side₁ side₂ : SquareTraceSide⦄ ⦃s t : ℝ⦄,
    s ∈ squareTraceSideParameterSet x₀ r side₁ →
    t ∈ squareTraceSideParameterSet x₀ r side₂ →
    |h.sideValue side₁ s - h.sideValue side₂ t| ^ 2 ≤ B

/-- Four sidewise increment estimates and the corner equalities in
`SquareSideTrace` give a uniform boundary oscillation estimate.  The constant
is exactly `8 * r` times the sum of the four side energies: a boundary route
can be chosen to use at most one portion of each side, and finite
Cauchy--Schwarz contributes the factor four. -/
theorem SquareSideTrace.hasBoundarySqOscillationLE_of_sideSqIncrementLE
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    (h : SquareSideTrace u g x₀ r) (hr : 0 ≤ r)
    {Eright Etop Eleft Ebottom : ℝ}
    (hEright : 0 ≤ Eright) (hEtop : 0 ≤ Etop)
    (hEleft : 0 ≤ Eleft) (hEbottom : 0 ≤ Ebottom)
    (hright : h.HasSideSqIncrementLE .right Eright)
    (htop : h.HasSideSqIncrementLE .top Etop)
    (hleft : h.HasSideSqIncrementLE .left Eleft)
    (hbottom : h.HasSideSqIncrementLE .bottom Ebottom) :
    h.HasBoundarySqOscillationLE (8 * r * (Eright + Etop + Eleft + Ebottom)) := by
  have hzero {E z : ℝ} (hE : 0 ≤ E) : |z - z| ^ 2 ≤ 2 * r * E := by
    rw [sub_self, abs_zero]
    norm_num
    exact mul_nonneg (mul_nonneg (by norm_num) hr) hE
  have hright' {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .right)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .right) :
      |h.right s - h.right t| ^ 2 ≤ 2 * r * Eright := by
    simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hright ht hs
  have htop' {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .top)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .top) :
      |h.top s - h.top t| ^ 2 ≤ 2 * r * Etop := by
    simpa only [SquareSideTrace.sideValue, abs_sub_comm] using htop ht hs
  have hleft' {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .left)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .left) :
      |h.left s - h.left t| ^ 2 ≤ 2 * r * Eleft := by
    simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hleft ht hs
  have hbottom' {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .bottom)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .bottom) :
      |h.bottom s - h.bottom t| ^ 2 ≤ 2 * r * Ebottom := by
    simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hbottom ht hs
  have hrightTop {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .right)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .top) :
      |h.right s - h.top t| ^ 2 ≤ 8 * r * (Eright + Etop + Eleft + Ebottom) := by
    have hRend : x₀ 1 + r ∈ squareTraceSideParameterSet x₀ r .right := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hTend : x₀ 0 + r ∈ squareTraceSideParameterSet x₀ r .top := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hchain := sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
      (E₀ := Eright) (E₁ := Eleft) (E₂ := Ebottom) (E₃ := Etop)
      (x₀ := h.right s) (x₁ := h.right (x₀ 1 + r))
      (x₂ := h.top (x₀ 0 + r)) (x₃ := h.top (x₀ 0 + r)) (x₄ := h.top t)
      (hright' hs hRend)
      (by rw [h.rightTop]; exact hzero hEleft)
      (hzero hEbottom)
      (htop' hTend ht)
    simpa only [add_comm, add_left_comm, add_assoc] using hchain
  have hrightLeft {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .right)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .left) :
      |h.right s - h.left t| ^ 2 ≤ 8 * r * (Eright + Etop + Eleft + Ebottom) := by
    have hRend : x₀ 1 + r ∈ squareTraceSideParameterSet x₀ r .right := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hTtop : x₀ 0 + r ∈ squareTraceSideParameterSet x₀ r .top := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hTbottom : x₀ 0 - r ∈ squareTraceSideParameterSet x₀ r .top := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hLtop : x₀ 1 + r ∈ squareTraceSideParameterSet x₀ r .left := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hchain := sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
      (E₀ := Eright) (E₁ := Etop) (E₂ := Eleft) (E₃ := Ebottom)
      (x₀ := h.right s) (x₁ := h.right (x₀ 1 + r))
      (x₂ := h.top (x₀ 0 - r)) (x₃ := h.left t) (x₄ := h.left t)
      (hright' hs hRend)
      (by rw [h.rightTop]; exact htop' hTtop hTbottom)
      (by rw [h.topLeft]; exact hleft' hLtop ht)
      (hzero hEbottom)
    simpa only [add_comm, add_left_comm, add_assoc] using hchain
  have hrightBottom {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .right)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .bottom) :
      |h.right s - h.bottom t| ^ 2 ≤ 8 * r * (Eright + Etop + Eleft + Ebottom) := by
    have hRstart : x₀ 1 - r ∈ squareTraceSideParameterSet x₀ r .right := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hBstart : x₀ 0 + r ∈ squareTraceSideParameterSet x₀ r .bottom := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hchain := sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
      (E₀ := Eright) (E₁ := Etop) (E₂ := Eleft) (E₃ := Ebottom)
      (x₀ := h.right s) (x₁ := h.right (x₀ 1 - r))
      (x₂ := h.bottom (x₀ 0 + r)) (x₃ := h.bottom (x₀ 0 + r)) (x₄ := h.bottom t)
      (hright' hs hRstart)
      (by rw [← h.bottomRight]; exact hzero hEtop)
      (hzero hEleft)
      (hbottom' hBstart ht)
    simpa only [add_comm, add_left_comm, add_assoc] using hchain
  have htopLeft {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .top)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .left) :
      |h.top s - h.left t| ^ 2 ≤ 8 * r * (Eright + Etop + Eleft + Ebottom) := by
    have hTstart : x₀ 0 - r ∈ squareTraceSideParameterSet x₀ r .top := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hLtop : x₀ 1 + r ∈ squareTraceSideParameterSet x₀ r .left := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hchain := sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
      (E₀ := Etop) (E₁ := Eright) (E₂ := Ebottom) (E₃ := Eleft)
      (x₀ := h.top s) (x₁ := h.top (x₀ 0 - r))
      (x₂ := h.left (x₀ 1 + r)) (x₃ := h.left (x₀ 1 + r)) (x₄ := h.left t)
      (htop' hs hTstart)
      (by rw [h.topLeft]; exact hzero hEright)
      (hzero hEbottom)
      (hleft' hLtop ht)
    simpa only [add_comm, add_left_comm, add_assoc] using hchain
  have htopBottom {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .top)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .bottom) :
      |h.top s - h.bottom t| ^ 2 ≤ 8 * r * (Eright + Etop + Eleft + Ebottom) := by
    have hTstart : x₀ 0 - r ∈ squareTraceSideParameterSet x₀ r .top := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hLtop : x₀ 1 + r ∈ squareTraceSideParameterSet x₀ r .left := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hLbottom : x₀ 1 - r ∈ squareTraceSideParameterSet x₀ r .left := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hBstart : x₀ 0 - r ∈ squareTraceSideParameterSet x₀ r .bottom := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hchain := sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
      (E₀ := Etop) (E₁ := Eleft) (E₂ := Ebottom) (E₃ := Eright)
      (x₀ := h.top s) (x₁ := h.top (x₀ 0 - r))
      (x₂ := h.left (x₀ 1 - r)) (x₃ := h.bottom t) (x₄ := h.bottom t)
      (htop' hs hTstart)
      (by rw [h.topLeft]; exact hleft' hLtop hLbottom)
      (by rw [h.leftBottom]; exact hbottom' hBstart ht)
      (hzero hEright)
    simpa only [add_comm, add_left_comm, add_assoc] using hchain
  have hleftBottom {s t : ℝ}
      (hs : s ∈ squareTraceSideParameterSet x₀ r .left)
      (ht : t ∈ squareTraceSideParameterSet x₀ r .bottom) :
      |h.left s - h.bottom t| ^ 2 ≤ 8 * r * (Eright + Etop + Eleft + Ebottom) := by
    have hLstart : x₀ 1 - r ∈ squareTraceSideParameterSet x₀ r .left := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hBstart : x₀ 0 - r ∈ squareTraceSideParameterSet x₀ r .bottom := by
      simp only [squareTraceSideParameterSet]
      constructor <;> linarith
    have hchain := sq_abs_sub_le_eight_mul_radius_mul_sum_of_four_side_chain
      (E₀ := Eleft) (E₁ := Eright) (E₂ := Etop) (E₃ := Ebottom)
      (x₀ := h.left s) (x₁ := h.left (x₀ 1 - r))
      (x₂ := h.bottom (x₀ 0 - r)) (x₃ := h.bottom (x₀ 0 - r)) (x₄ := h.bottom t)
      (hleft' hs hLstart)
      (by rw [h.leftBottom]; exact hzero hEright)
      (hzero hEtop)
      (hbottom' hBstart ht)
    simpa only [add_comm, add_left_comm, add_assoc] using hchain
  intro side₁ side₂ s t hs ht
  cases side₁ <;> cases side₂
  · exact sq_abs_sub_le_eight_mul_radius_mul_sum_of_one_side
      (E₀ := Eright) (E₁ := Etop) (E₂ := Eleft) (E₃ := Ebottom)
      hr hEright hEtop hEleft hEbottom
      (hright' hs ht)
  · exact hrightTop hs ht
  · exact hrightLeft hs ht
  · exact hrightBottom hs ht
  · simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hrightTop ht hs
  · simpa only [SquareSideTrace.sideValue, add_comm, add_left_comm, add_assoc] using
      (sq_abs_sub_le_eight_mul_radius_mul_sum_of_one_side
        (E₀ := Etop) (E₁ := Eright) (E₂ := Eleft) (E₃ := Ebottom)
        hr hEtop hEright hEleft hEbottom
        (htop' hs ht))
  · exact htopLeft hs ht
  · exact htopBottom hs ht
  · simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hrightLeft ht hs
  · simpa only [SquareSideTrace.sideValue, abs_sub_comm] using htopLeft ht hs
  · simpa only [SquareSideTrace.sideValue, add_comm, add_left_comm, add_assoc] using
      (sq_abs_sub_le_eight_mul_radius_mul_sum_of_one_side
        (E₀ := Eleft) (E₁ := Eright) (E₂ := Etop) (E₃ := Ebottom)
        hr hEleft hEright hEtop hEbottom
        (hleft' hs ht))
  · exact hleftBottom hs ht
  · simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hrightBottom ht hs
  · simpa only [SquareSideTrace.sideValue, abs_sub_comm] using htopBottom ht hs
  · simpa only [SquareSideTrace.sideValue, abs_sub_comm] using hleftBottom ht hs
  · simpa only [SquareSideTrace.sideValue, add_comm, add_left_comm, add_assoc] using
      (sq_abs_sub_le_eight_mul_radius_mul_sum_of_one_side
        (E₀ := Ebottom) (E₁ := Eright) (E₂ := Etop) (E₃ := Eleft)
        hr hEbottom hEright hEtop hEleft
        (hbottom' hs ht))

end

end PDE
