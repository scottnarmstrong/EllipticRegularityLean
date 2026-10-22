module

public import EllipticRegularity.Guerra.SymmetrizeProof

@[expose] public section

namespace PDE

/-- Symmetrization of a flux (Lemma 4.31). For `k ≥ 1` there is one
choice, measurable entrywise as a function of the entries of `C` and of `p`, `S(C,p)` such that whenever `C` satisfies
`ξ·Cξ ≥ k⁻¹|ξ|²` and `ξ·C⁻¹ξ ≥ k⁻¹|ξ|²` (matrix inverse; invertibility is implied for `d ≥ 1`),
`S(C,p)` is symmetric, `S(C,p) p = C p` and `(2k)⁻¹|ξ|² ≤ ξ·Sξ ≤ 2k|ξ|²`. -/
theorem guerra_symmetrize (d : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    ∃ S : Mat d → Vec d → Mat d,
      (∀ i j : Fin d, Measurable
        (fun q : (Fin d → Fin d → ℝ) × Vec d => S (Matrix.of q.1) q.2 i j)) ∧
      ∀ (C : Mat d) (p : Vec d),
        (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C ξ)) →
        (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C⁻¹ ξ)) →
        (∀ i j : Fin d, S C p i j = S C p j i) ∧
        matVecMul (S C p) p = matVecMul C p ∧
        (∀ ξ : Vec d, (2 * k)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (S C p) ξ)) ∧
        (∀ ξ : Vec d, vecDot ξ (matVecMul (S C p) ξ) ≤ 2 * k * vecNormSq ξ) := by exact PDE.GuerraSymmetrizeProof.result d k hk

end PDE
