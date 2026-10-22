module

public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Nested cylinders for the parabolic weak Harnack inequality

The three families of space-time cylinders used in the proof of Proposition 5.13
(manuscript), each parametrized by `σ ∈ [1/2, 1]`, increasing in
`σ`. The gap between `σ' < σ` is `(σ - σ')/2` (positive family) or `(σ - σ')/4` (negative families)
in space and a fixed multiple of `σ - σ'` in time (`/4`, `/16`, `/8` respectively), on the side where the cutoff vanishes.

* `posCyl`: from `Q⁻ = B_{1/2} × (-3/4,-1/2)` (`σ = 1/2`) to `B_{3/4} × (-7/8,-3/8)` (`σ = 1`), with gaps
  at both time ends (positive powers, cutoffs vanishing at the top time).
* `negCyl`: from `B_{5/8} × (-5/16,0]` (`σ = 1/2`) to `B_{3/4} × (-11/32,0]` (`σ = 1`), sharing the top
  time `0` (negative powers, cutoffs vanishing at the bottom time). It stops short of `-3/8` so that the
  level time `t₀` of the logarithmic estimate can be any good time in `(-3/8, -11/32)`.
* `negCylInner`: from `Q⁺ = B_{1/2} × (-1/4,0]` (`σ = 1/2`) to `B_{5/8} × (-5/16,0]` (`σ = 1`).
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open Set

variable {d : ℕ}

/-- Positive-power family: `B_{1/2+(σ-1/2)/2} × (-3/4-(σ-1/2)/4, -1/2+(σ-1/2)/4)`. -/
def posCyl (d : ℕ) (σ : ℝ) : Set (Vec d × ℝ) :=
  euclideanBall (0 : Vec d) (1 / 2 + (σ - 1 / 2) / 2) ×ˢ
    Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4)

/-- Negative-power family for the Bombieri-Giusti step:
`B_{5/8+(σ-1/2)/4} × (-5/16-(σ-1/2)/16, 0]`. -/
def negCyl (d : ℕ) (σ : ℝ) : Set (Vec d × ℝ) :=
  euclideanBall (0 : Vec d) (5 / 8 + (σ - 1 / 2) / 4) ×ˢ Ioc (-5 / 16 - (σ - 1 / 2) / 16) 0

/-- Negative-power family for the final iteration to `L^∞`:
`B_{1/2+(σ-1/2)/4} × (-1/4-(σ-1/2)/8, 0]`. -/
def negCylInner (d : ℕ) (σ : ℝ) : Set (Vec d × ℝ) :=
  euclideanBall (0 : Vec d) (1 / 2 + (σ - 1 / 2) / 4) ×ˢ Ioc (-1 / 4 - (σ - 1 / 2) / 8) 0

theorem posCyl_half : posCyl d (1 / 2) =
    euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2) := by
  norm_num [posCyl]

theorem posCyl_one : posCyl d 1 =
    euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioo (-7 / 8 : ℝ) (-3 / 8) := by
  norm_num [posCyl]

theorem negCyl_half : negCyl d (1 / 2) =
    euclideanBall (0 : Vec d) (5 / 8) ×ˢ Ioc (-5 / 16 : ℝ) 0 := by
  norm_num [negCyl]

theorem negCyl_one : negCyl d 1 =
    euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioc (-11 / 32 : ℝ) 0 := by
  norm_num [negCyl]

theorem negCylInner_half : negCylInner d (1 / 2) =
    euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0 := by
  norm_num [negCylInner]

theorem negCylInner_one : negCylInner d 1 = negCyl d (1 / 2) := by
  norm_num [negCylInner, negCyl]

end PDE.Parabolic.WeakHarnack
