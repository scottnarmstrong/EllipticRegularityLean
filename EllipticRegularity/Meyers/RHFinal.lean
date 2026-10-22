module

public import EllipticRegularity.Meyers.Assembly
public import EllipticRegularity.Meyers.RHInteriorAE
public import SobolevStatements.ConvexSobolevPoincare

/-!
# The interior reverse Hölder interface, instantiated

`MeyersAssembly.MeyersRHInterior d` follows from `PDE.MeyersRH.rh_interior_of_aemeasurable`,
with the convex Sobolev--Poincaré hypothesis discharged by
`PDE.exists_convexSobolevPoincare_constant`.
-/

@[expose] public section

namespace PDE

/-- The interior reverse Hölder inequality (Lemma 4.5(i)) with no interface hypotheses. -/
theorem meyers_rh_interior_final (d : ℕ) (hd : 2 ≤ d) : MeyersAssembly.MeyersRHInterior d := by
  obtain ⟨C0, hC0, h⟩ := MeyersRH.rh_interior_of_aemeasurable d hd
    (exists_convexSobolevPoincare_constant d hd)
  exact ⟨C0, hC0, h⟩

end PDE
