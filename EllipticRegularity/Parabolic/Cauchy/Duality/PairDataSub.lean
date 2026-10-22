module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairDataNeg

@[expose] public section

namespace PDE.Parabolic.Duality

open PDE.Parabolic.Energy

/-- Subtract compatible abstract energy data on a common collar. -/
noncomputable def energyDataSub {d : ℕ} (D E : Energy.Data d)
    (hK : D.K = E.K) (hδ : D.δ0 = E.δ0) (hs : D.s = E.s) (ht : D.t = E.t) :
    Energy.Data d := energyDataAdd D (energyDataNeg E) hK hδ hs ht

theorem energyDataAdd_fields {d : ℕ} (D E : Energy.Data d)
    (hK : D.K = E.K) (hδ : D.δ0 = E.δ0) (hs : D.s = E.s) (ht : D.t = E.t)
    (z : Vec d × ℝ) :
    (energyDataAdd D E hK hδ hs ht).u z = D.u z + E.u z ∧
      (energyDataAdd D E hK hδ hs ht).Du z = D.Du z + E.Du z ∧
      (energyDataAdd D E hK hδ hs ht).G z = D.G z + E.G z := by
  simp [energyDataAdd]

theorem energyDataSub_fields {d : ℕ} (D E : Energy.Data d)
    (hK : D.K = E.K) (hδ : D.δ0 = E.δ0) (hs : D.s = E.s) (ht : D.t = E.t)
    (z : Vec d × ℝ) :
    (energyDataSub D E hK hδ hs ht).u z = D.u z - E.u z ∧
      (energyDataSub D E hK hδ hs ht).Du z = D.Du z - E.Du z ∧
      (energyDataSub D E hK hδ hs ht).G z = D.G z - E.G z := by
  simp [energyDataSub, energyDataAdd, energyDataNeg, sub_eq_add_neg]

end PDE.Parabolic.Duality
