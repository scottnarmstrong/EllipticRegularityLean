module

public import PDEFoundation.Monotonicity.FriedlandHaymanProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Friedland--Hayman inequality for complementary spherical domains (Lemma 2.11). -/
theorem friedland_hayman (d : ℕ) (hd : 2 ≤ d) (Ωp Ωm : Set (Vec d))
    (hp : ∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1)
    (hm : ∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1)
    (hdisj : Disjoint Ωp Ωm)
    (hcover : closure Ωp ∪ closure Ωm = euclideanSphere (0 : Vec d) 1) :
    2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
      eigenvalueDegree d (sphereDirichletEigenvalue d Ωm) := by exact PDE.FriedlandHaymanProof.result d hd Ωp Ωm hp hm hdisj hcover

end PDE
