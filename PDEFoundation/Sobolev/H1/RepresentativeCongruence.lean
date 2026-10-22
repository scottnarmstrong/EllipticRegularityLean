module

public import PDEFoundation.Sobolev.H1.Basic

/-!
# Congruence of `H¹` representatives

Concrete `H1Function` values retain a chosen weak-gradient representative.
On an open domain, two such bundles with the same value representative have
coordinatewise almost-everywhere equal gradients.  This is the bridge needed
when a representative-level `H¹₀` membership witness supplies its own chosen
gradient.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory

namespace H1Function

/-- Two `H¹` representatives with the same concrete value have
almost-everywhere equal chosen weak-gradient coordinates on an open domain. -/
theorem grad_coord_ae_eq_of_toFun_eq
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u v : H1Function U) (hvalue : u.toFun = v.toFun) (i : Fin d) :
    (fun x => u.grad x i) =ᵐ[volumeOn U] fun x => v.grad x i := by
  have hu := u.hasWeakGradient i
  rw [hvalue] at hu
  exact HasWeakPartialDerivOn.ae_eq hU
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((u.gradMemL2 i).locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((v.gradMemL2 i).locallyIntegrable (by norm_num)))
    hu (v.hasWeakGradient i)

end H1Function

end PDE
