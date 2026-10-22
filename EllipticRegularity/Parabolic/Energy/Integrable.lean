module

public import EllipticRegularity.Parabolic.Energy.Limit

/-!
# Integrability of the two integrands of the energy identity
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

theorem memLp_u : MemLp D.u 2 D.μP := (D.conv_mollT D.hu2).1

theorem memLp_Du (i : Fin d) : MemLp (fun z => D.Du z i) 2 D.μP := (D.conv_mollT (D.hDu2 i)).1

theorem memLp_G (i : Fin d) : MemLp (fun z => D.G z i) 2 D.μP := (D.conv_mollT (D.hG2 i)).1

theorem integrable_A :
    Integrable (fun z => D.u z ^ 2 * D.φ z * parTimeDeriv D.φ z) D.μP := by
  have hw : Continuous fun z : Vec d × ℝ => D.φ z * parTimeDeriv D.φ z :=
    D.phi_continuous.mul D.parTimeDeriv_continuous
  obtain ⟨M, hM⟩ := D.ae_bound_on_slab hw
  have := (D.memLp_u.integrable_sq).bdd_mul hw.aestronglyMeasurable (c := M)
    (hM.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  ring

theorem integrable_B :
    Integrable (fun z => ∑ i, D.G z i *
      (D.φ z ^ 2 * D.Du z i + 2 * D.φ z * D.u z * parSpaceGrad D.φ z i)) D.μP := by
  refine integrable_finsetSum _ fun i _ => ?_
  have hw1 : Continuous fun z : Vec d × ℝ => D.φ z ^ 2 := D.phi_continuous.pow 2
  have hw2 : Continuous fun z : Vec d × ℝ => 2 * D.φ z * parSpaceGrad D.φ z i :=
    (continuous_const.mul D.phi_continuous).mul (D.parSpaceGrad_continuous i)
  obtain ⟨M1, hM1⟩ := D.ae_bound_on_slab hw1
  obtain ⟨M2, hM2⟩ := D.ae_bound_on_slab hw2
  have h1 := integrable_weight_mul hw1.aestronglyMeasurable hM1 (D.memLp_G i) (D.memLp_Du i)
  have h2 := integrable_weight_mul hw2.aestronglyMeasurable hM2 (D.memLp_G i) D.memLp_u
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  ring

end Data

end PDE.Parabolic.Energy
