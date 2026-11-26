module

public import BSlocalmax.Balls

/-!
# Main result: sharp `L^∞`–`L²` estimate for subsolutions on balls, `d ≥ 2`

**Proposition 1.** Let `d ≥ 2`. There exists `C = C(d) < ∞` such that for every
`u ∈ H¹(B₁)` satisfying `-∇·(a ∇u) ≤ 0` in `B₁` we have

  `ess sup_{B_{1/2}} u₊ ≤ C (ℓ(Λ) Λ)^{(d-1)/4} ‖u‖_{L²(B₁)}`,

where `ℓ(s) = log(e + s)` if `d = 3` and `ℓ(s) = 1` otherwise (`ell`).

Conventions: `B_r = euclideanBall 0 r` is the Euclidean ball, `a` is a measurable coefficient field
with `IsEllipticMatrix 1 Λ (a x)`, i.e. `|ξ|² ≤ ξ·a(x)ξ` and `Λ⁻¹|ξ|² ≤ ξ·a(x)⁻¹ξ`, and the
inequality `-∇·(a ∇u) ≤ 0` is understood weakly (`IsWeakDivergenceFormSubharmonicOn`).

Proof: `exists_sharpLocalMax_constant_ball` (`Balls.lean`), which rescales the estimate on
cubes (`CubeMain.lean`) and covers the half ball by finitely many small balls.
-/

@[expose] public section

namespace PDE.BSlocalmax

open MeasureTheory PDE

/-- **Proposition 1** (sharp `L^∞` estimate for subsolutions on balls, `d ≥ 2`). -/
theorem proposition1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  exists_sharpLocalMax_constant_ball d hd

end PDE.BSlocalmax
