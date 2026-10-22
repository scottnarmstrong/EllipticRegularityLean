module

public import EllipticRegularity.Ch4.GreenFunction.D3
public import EllipticRegularity.Ch4.GreenDecay.DirichletFull
public import EllipticRegularity.Ch4.GreenDecay.MaxPrincipleFull
public import PDEFoundation
public import EllipticRegularity.Green.GreenFunctionDef

/-!
# Proof of `PDE.greenD3` (Proposition 4.42)

-/

@[expose] public section

namespace PDE.GreenD3Proof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) :
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
  PDE.Ch4Green.greenD3_full  d hd (PDE.Ch4GreenDecay.greenDirichlet_full d (by omega)) (PDE.Ch4GreenDecay.greenMaxPrinciple_full d (by omega))

end PDE.GreenD3Proof
