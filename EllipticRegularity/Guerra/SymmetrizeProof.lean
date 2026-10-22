module

public import PDEFoundation
public import EllipticRegularity.Guerra.Symmetrize.Result

/-!
# Proof of `PDE.guerra_symmetrize` (Lemma 4.31)

Proof of the statement `PDE.guerra_symmetrize` by the explicit formula
`A = σ Id + e ⊗ z + z ⊗ e + (2/σ) z ⊗ z` of the manuscript (helper module
`EllipticRegularity.Guerra.Symmetrize.Result`).
-/

@[expose] public section

namespace PDE.GuerraSymmetrizeProof

theorem result (d : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    ∃ S : Mat d → Vec d → Mat d,
      (∀ i j : Fin d, Measurable
        (fun q : (Fin d → Fin d → ℝ) × Vec d => S (Matrix.of q.1) q.2 i j)) ∧
      ∀ (C : Mat d) (p : Vec d),
        (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C ξ)) →
        (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C⁻¹ ξ)) →
        (∀ i j : Fin d, S C p i j = S C p j i) ∧
        matVecMul (S C p) p = matVecMul C p ∧
        (∀ ξ : Vec d, (2 * k)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (S C p) ξ)) ∧
        (∀ ξ : Vec d, vecDot ξ (matVecMul (S C p) ξ) ≤ 2 * k * vecNormSq ξ) :=
  symmetrizer_exists d k hk

end PDE.GuerraSymmetrizeProof
