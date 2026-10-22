module

public import PDEFoundation.Monotonicity.FriedlandHaymanOfDisjointProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Friedland--Hayman inequality for disjoint spherical domains, the form used in the proof of Theorem 2.13 (Lemma 2.11). -/
theorem friedland_hayman_of_disjoint (d : ℕ) (hd : 2 ≤ d) (Ωp Ωm : Set (Vec d))
    (hp : ∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1)
    (hm : ∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1)
    (hdisj : Disjoint Ωp Ωm) :
    2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
      eigenvalueDegree d (sphereDirichletEigenvalue d Ωm) := by exact PDE.FriedlandHaymanOfDisjointProof.result d hd Ωp Ωm hp hm hdisj

end PDE
