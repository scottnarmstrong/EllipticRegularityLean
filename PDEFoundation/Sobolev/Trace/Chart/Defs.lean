module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Geometry.EuclideanBall

/-!
# Graph charts of a `C¹` boundary

A graph chart of `Ω ⊆ Vec (n+1)` singles out a coordinate `i`, a sign `sgn = ±1` and a globally
`C¹`, Lipschitz function `γ : Vec n → ℝ`, and identifies the cylinder
`U = Ψ (B_r(c) × (-a, a))`, `Ψ(x', t) = insertNth i (γ x' + sgn t) x'`, with the model:
`Ω ∩ U = Ψ (B_r(c) × (0, a))`.  The map `Ψ` is a shear followed by a coordinate insertion, so it is
volume preserving with an explicit inverse; the boundary piece is the graph `Ψ (B_r(c) × {0})`.

A trace atlas is a finite family of graph charts with a smooth partition of unity subordinate to
the chart cylinders whose sum is one near `∂Ω`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set

/-- The chart map `Ψ(x', t) = insertNth i (γ x' + sgn t) x'`. -/
def graphMap {n : ℕ} (i : Fin (n + 1)) (γ : Vec n → ℝ) (sgn : ℝ) (z : Vec n × ℝ) : Vec (n + 1) :=
  Fin.insertNth i (γ z.1 + sgn * z.2) z.1

/-- Inverse of the chart map: `x ↦ (x ∘ succAbove i, sgn (x i - γ (x ∘ succAbove i)))`
(for `sgn = ±1`). -/
def graphMapInv {n : ℕ} (i : Fin (n + 1)) (γ : Vec n → ℝ) (sgn : ℝ) (x : Vec (n + 1)) :
    Vec n × ℝ :=
  (fun j => x (i.succAbove j), sgn * (x i - γ (fun j => x (i.succAbove j))))

/-- A graph chart of `Ω` (see the module docstring). -/
structure GraphChart {n : ℕ} (Ω : Set (Vec (n + 1))) where
  i : Fin (n + 1)
  sgn : ℝ
  sgn_sq : sgn ^ 2 = 1
  γ : Vec n → ℝ
  γ_contDiff : ContDiff ℝ 1 γ
  L : ℝ
  L_nonneg : 0 ≤ L
  γ_lip : ∀ x' y' : Vec n, |γ x' - γ y'| ≤ L * vecEuclideanNorm (x' - y')
  c : Vec n
  r : ℝ
  a : ℝ
  r_pos : 0 < r
  a_pos : 0 < a
  inter_eq : Ω ∩ graphMap i γ sgn '' (euclideanBall c r ×ˢ Ioo (-a) a) =
    graphMap i γ sgn '' (euclideanBall c r ×ˢ Ioo 0 a)

namespace GraphChart

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The chart map of a chart. -/
def map (φ : GraphChart Ω) : Vec n × ℝ → Vec (n + 1) := graphMap φ.i φ.γ φ.sgn

/-- The inverse chart map. -/
def inv (φ : GraphChart Ω) : Vec (n + 1) → Vec n × ℝ := graphMapInv φ.i φ.γ φ.sgn

/-- The chart cylinder `U`. -/
def dom (φ : GraphChart Ω) : Set (Vec (n + 1)) := φ.map '' (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a)

end GraphChart

/-- A trace atlas: finitely many graph charts and a smooth partition of unity near `∂Ω`. -/
structure TraceAtlas {n : ℕ} (Ω : Set (Vec (n + 1))) where
  N : ℕ
  chart : Fin N → GraphChart Ω
  ζ : Fin N → Vec (n + 1) → ℝ
  ζ_smooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ζ j)
  ζ_nonneg : ∀ j x, 0 ≤ ζ j x
  ζ_compact : ∀ j, HasCompactSupport (ζ j)
  ζ_tsupport : ∀ j, tsupport (ζ j) ⊆ (chart j).dom
  V : Set (Vec (n + 1))
  V_open : IsOpen V
  frontier_subset : frontier Ω ⊆ V
  sum_eq_one : ∀ x ∈ V, ∑ j, ζ j x = 1

end PDE.TraceLane
