module

public import PDEFoundation.Sobolev.Cutoff.Cube

/-!
# Cube cutoffs for the Meyers reverse Hölder inequality

For the cube `Q = centeredAxisCube z r` the reverse Hölder step needs a cutoff equal to one
on `Q` with support in the concentric cube `2Q`. The repository provides a *smooth* cutoff
of this type with Euclidean gradient bound `32 d / r`; the (Lipschitz, `4 / ℓ(Q)`) cutoff of
the manuscript is replaced by it since only the dimension-dependence of the constants matters
and the smooth multiplier calculus is already available for `H¹`.
-/

@[expose] public section

namespace PDE.MeyersRH

/-- A smooth cutoff, equal to one on `Q = centeredAxisCube z r`, with compact support inside
`2Q = centeredAxisCube z (2 r)`, `0 ≤ η ≤ 1` and `|∇η| ≤ 32 d / r`. -/
noncomputable def cubeCutoff {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 < r) :
    QuantitativeSmoothCutoff (centeredAxisCube z r) (centeredAxisCube z (2 * r))
      ((32 * (d : ℝ)) / r) :=
  (quantitativeCenteredAxisCubeCutoff z hr).reindex
    (fun x hx => by
      rw [centeredAxisCube_eq_metric_ball z hr] at hx
      rw [closedCenteredAxisCube_eq_metric_closedBall z hr.le]
      exact Metric.ball_subset_closedBall hx)
    subset_rfl

end PDE.MeyersRH
