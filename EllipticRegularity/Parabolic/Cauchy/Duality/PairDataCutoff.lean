module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairDataPolarization

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set
open PDE.Parabolic.Energy

/-- A time-independent cutoff and cancellation of the bulk flux terms turn the polarized
abstract energy identity into the boundary-flux product rule. -/
theorem energyData_cross_identity_spatial_cutoff {d : ℕ} (D E : Energy.Data d)
    (hK : D.K = E.K) (hδ : D.δ0 = E.δ0)
    (hs : D.s = E.s) (ht : D.t = E.t)
    (hφt : ∀ z : Vec d × ℝ, parTimeDeriv D.φ z = 0)
    (hbulk : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc D.s D.t)),
      (∑ i : Fin d, (D.G z i * E.Du z i + E.G z i * D.Du z i)) = 0) :
    (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) * E.u (x, D.t)) -
        ∫ x in D.K, D.φ (x, D.s) ^ 2 * D.u (x, D.s) * E.u (x, D.s) =
      -∫ z in D.K ×ˢ Ioc D.s D.t,
        2 * D.φ z * ∑ i,
          (D.G z i * E.u z + E.G z i * D.u z) * parSpaceGrad D.φ z i := by
  have hid := energyData_cross_identity D E hK hδ hs ht
  have hpoint : ∀ᵐ z ∂(volume.restrict (D.K ×ˢ Ioc D.s D.t)),
      2 * D.u z * E.u z * D.φ z * parTimeDeriv D.φ z -
        ∑ i,
          (D.G z i * (D.φ z ^ 2 * E.Du z i +
              2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
            E.G z i * (D.φ z ^ 2 * D.Du z i +
              2 * D.φ z * D.u z * parSpaceGrad D.φ z i)) =
      -(2 * D.φ z * ∑ i,
          (D.G z i * E.u z + E.G z i * D.u z) * parSpaceGrad D.φ z i) := by
    filter_upwards [hbulk] with z hb
    rw [hφt z]
    have hsum :
        ∑ i : Fin d,
          (D.G z i * (D.φ z ^ 2 * E.Du z i +
              2 * D.φ z * E.u z * parSpaceGrad D.φ z i) +
            E.G z i * (D.φ z ^ 2 * D.Du z i +
              2 * D.φ z * D.u z * parSpaceGrad D.φ z i)) =
          D.φ z ^ 2 *
              (∑ i : Fin d, (D.G z i * E.Du z i + E.G z i * D.Du z i)) +
            2 * D.φ z * (∑ i : Fin d,
              (D.G z i * E.u z + E.G z i * D.u z) * parSpaceGrad D.φ z i) := by
      calc
        _ = ∑ i : Fin d,
            (D.φ z ^ 2 * (D.G z i * E.Du z i + E.G z i * D.Du z i) +
              2 * D.φ z *
                ((D.G z i * E.u z + E.G z i * D.u z) * parSpaceGrad D.φ z i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum, hb]
    ring
  rw [hid]
  rw [← integral_neg]
  exact integral_congr_ae hpoint

end PDE.Parabolic.Duality
