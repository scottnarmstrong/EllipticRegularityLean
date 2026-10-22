module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyFinal

/-!
# Proof of `PDE.exists_newtonPotential_weakTypeOne`

`PDE.NewtonWeakTypeProof.result`: the local weak-type (1,1) estimate for `∇ u_F`, proved by the
Calderón–Zygmund decomposition of `F` at height `λ` (`WeakType/Decomposition*`), the `L²` energy
bound for the good part (`WeakType/Energy*`), the Hörmander estimate for the bad parts
(`WeakType/Hormander*`), and a mollification/truncation argument that reduces the nonsmooth pieces
to smooth compactly supported fields (`WeakType/Mollify*`, `WeakType/Truncate*`,
`WeakType/Assembly*`).
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace NewtonWeakTypeProof

theorem result (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) :=
  PDE.NewtonWeakType.exists_weakType d hd

end NewtonWeakTypeProof

end PDE
