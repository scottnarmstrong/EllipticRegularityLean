module

public import EllipticRegularity.Ch4.GreenD3Proof

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory

/-- Two-sided Green function bounds (Proposition 4.42), `d ≥ 3`.  There is `C > 0`, depending only on `d`,
such that for every `Λ`, `R > 0`, every measurable coefficient field `a` on `B_R` with `IsEllipticMatrix 1 Λ (a x)`
on `B_R` and every Green function `G` of `-div (a ∇ ·)` in `B_R` with pole at `0`: on each annulus
`B_r \ B_{r/2}`, `r ≤ R/2`, `exp (-C √Λ) r^{2-d} ≤ G ≤ exp (C √Λ) r^{2-d}` almost everywhere; and the same
bounds hold pointwise on `0 < |x| ≤ R/2` for any representative `Gc` of `G` that is continuous on
`B_R \ {0}`. -/
theorem greenD3 (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 0 < R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ G : Vec d → ℝ, IsGreenFunction a R G →
        (∀ r : ℝ, 0 < r → r ≤ R / 2 →
          ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))),
            Real.exp (-(C * Real.sqrt Λ)) * r ^ (2 - (d : ℝ)) ≤ G x ∧
            G x ≤ Real.exp (C * Real.sqrt Λ) * r ^ (2 - (d : ℝ))) ∧
        (∀ Gc : Vec d → ℝ, ContinuousOn Gc (euclideanBall (0 : Vec d) R \ {0}) →
          Gc =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G →
          ∀ x : Vec d, 0 < vecEuclideanNorm x → vecEuclideanNorm x ≤ R / 2 →
            Real.exp (-(C * Real.sqrt Λ)) * vecEuclideanNorm x ^ (2 - (d : ℝ)) ≤ Gc x ∧
            Gc x ≤ Real.exp (C * Real.sqrt Λ) * vecEuclideanNorm x ^ (2 - (d : ℝ))) :=
  PDE.GreenD3Proof.result d hd

end PDE
