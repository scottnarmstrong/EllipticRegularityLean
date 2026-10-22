module

public import PDEFoundation.Monotonicity.Defs
import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.TheoremG

/-!
# Proof of `PDE.friedland_hayman_of_disjoint` (Theorem 2.13)

The proof is the Beckner--Kenig--Pipher route. Suspend each set
into `S^{n+N-1}`; this keeps its normalized measure and does not increase its exponent. Apply the
spherical Pólya--Szegő inequality there (polarization and a compactness argument). Transport the
resulting zonal problem to the Gaussian line by the 1-D Caffarelli contraction. Let `N → ∞` to get
`α(Ω) ≥ β(t_{|Ω|})`, where `β` is the Gaussian half-line Dirichlet eigenvalue. Conclude with the
Beckner--Kenig--Pipher inequality `β(t) + β(-t) ≥ 2`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.FriedlandHaymanOfDisjointProof

theorem result (d : ℕ) (hd : 2 ≤ d) (Ωp Ωm : Set (Vec d))
    (hp : ∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1)
    (hm : ∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1)
    (hdisj : Disjoint Ωp Ωm) :
    2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
      eigenvalueDegree d (sphereDirichletEigenvalue d Ωm) :=
  PDE.FHLane.fh_of_disjoint d hd Ωp Ωm hp hm hdisj

end PDE.FriedlandHaymanOfDisjointProof
