module

public import PDEFoundation.Monotonicity.Defs
import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.TheoremG

/-!
# Proof of `PDE.friedland_hayman` (Lemma 2.11)

The complementary form follows from the disjoint form `PDE.FHLane.fh_of_disjoint`, which does not
use the covering hypothesis. That form is proved by the Beckner--Kenig--Pipher route:
suspension, spherical Pólya--Szegő, transport to the Gaussian
line, the limit of large dimension, and the inequality `β(t) + β(-t) ≥ 2`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.FriedlandHaymanProof

theorem result (d : ℕ) (hd : 2 ≤ d) (Ωp Ωm : Set (Vec d))
    (hp : ∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1)
    (hm : ∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1)
    (hdisj : Disjoint Ωp Ωm)
    (_hcover : closure Ωp ∪ closure Ωm = euclideanSphere (0 : Vec d) 1) :
    2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
      eigenvalueDegree d (sphereDirichletEigenvalue d Ωm) :=
  PDE.FHLane.fh_of_disjoint d hd Ωp Ωm hp hm hdisj

end PDE.FriedlandHaymanProof
