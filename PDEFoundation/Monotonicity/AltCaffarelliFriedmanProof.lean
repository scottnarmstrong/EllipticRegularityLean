module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Monotonicity.ACF.Assembly
import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.TheoremG

/-!
# Proof of `PDE.alt_caffarelli_friedman` (Theorem 2.13)

The Alt–Caffarelli–Friedman monotonicity formula: the conditional assembly
`alt_caffarelli_friedman_of_friedlandHayman` applied to the proved Friedland–Hayman inequality for
disjoint spherical domains.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.AltCaffarelliFriedmanProof

theorem result (d : ℕ) (hd : 3 ≤ d) (R : ℝ) (hR : 0 < R)
    (up um : H1Function (euclideanBall (0 : Vec d) R))
    (hup_cont : ContinuousOn up.toFun (euclideanBall (0 : Vec d) R))
    (hum_cont : ContinuousOn um.toFun (euclideanBall (0 : Vec d) R))
    (hup_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ up.toFun x)
    (hum_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ um.toFun x)
    (hup_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) up)
    (hum_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) um)
    (hup0 : up.toFun 0 = 0) (hum0 : um.toFun 0 = 0)
    (hdisj : ∀ x ∈ euclideanBall (0 : Vec d) R, up.toFun x * um.toFun x = 0) :
    MonotoneOn (acfFunctional up.grad um.grad) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R, acfFunctional up.grad um.grad r ≠ ⊤ :=
  alt_caffarelli_friedman_of_friedlandHayman d hd R hR up um hup_cont hum_cont hup_nonneg hum_nonneg
    hup_sub hum_sub hup0 hum0 hdisj (fun h2 Ωp Ωm hp hm hdj =>
      PDE.FHLane.fh_of_disjoint d h2 Ωp Ωm hp hm hdj)

end PDE.AltCaffarelliFriedmanProof
