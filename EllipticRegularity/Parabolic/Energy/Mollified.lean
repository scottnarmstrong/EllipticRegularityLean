module

public import EllipticRegularity.Parabolic.Energy.IBP

/-!
# The mollified energy identity in space-time form
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

/-- The second integrand after integration by parts. -/
noncomputable def S (a : ℝ) (z : Vec d × ℝ) : ℝ :=
  ∑ i, mollT a D.K1 (fun z => D.G z i) z *
    (D.φ z ^ 2 * mollT a D.K1 (fun z => D.Du z i) z + 2 * D.φ z * D.v a z * parSpaceGrad D.φ z i)

theorem memLp_mollG {a : ℝ} (ha : 0 < a) (i : Fin d) :
    MemLp (mollT a D.K1 fun z => D.G z i) 2 D.μP :=
  memLp_mollT D.K1_compact (D.hG2 i) ha

theorem memLp_mollDu {a : ℝ} (ha : 0 < a) (i : Fin d) :
    MemLp (mollT a D.K1 fun z => D.Du z i) 2 D.μP :=
  memLp_mollT D.K1_compact (D.hDu2 i) ha

theorem memLp_v {a : ℝ} (ha : 0 < a) : MemLp (D.v a) 2 D.μP :=
  memLp_mollT D.K1_compact D.hu2 ha

theorem S_integrable {a : ℝ} (ha : 0 < a) : Integrable (D.S a) D.μP := by
  unfold S
  refine integrable_finsetSum _ fun i _ => ?_
  have hw1 : Continuous fun z : Vec d × ℝ => D.φ z ^ 2 := D.phi_continuous.pow 2
  have hw2 : Continuous fun z : Vec d × ℝ => 2 * D.φ z * parSpaceGrad D.φ z i :=
    (continuous_const.mul D.phi_continuous).mul (D.parSpaceGrad_continuous i)
  obtain ⟨M1, hM1⟩ := D.ae_bound_on_slab hw1
  obtain ⟨M2, hM2⟩ := D.ae_bound_on_slab hw2
  have h1 := integrable_weight_mul hw1.aestronglyMeasurable hM1
    (D.memLp_mollG ha i) (D.memLp_mollDu ha i)
  have h2 := integrable_weight_mul hw2.aestronglyMeasurable hM2
    (D.memLp_mollG ha i) (D.memLp_v ha)
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  ring

theorem ae_G_slice_integrable :
    ∀ᵐ σ ∂(volume.restrict (Ioc D.s D.t)), ∀ i, Integrable (fun y => D.G (y, σ) i)
      (volume.restrict D.K1) := by
  rw [ae_all_iff]
  intro i
  have h := D.integrableOn_G i
  unfold IntegrableOn at h
  rw [volume_restrict_prod] at h
  exact h.prod_left_ae

theorem integral_H2_eq {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    ∫ z, D.H2 a z ∂D.μP = -∫ z, D.S a z ∂D.μP := by
  have hH2 := D.H2_integrable ha haδ
  have hS := D.S_integrable ha
  rw [μP_eq] at hH2 hS ⊢
  rw [integral_prod_symm _ hH2, integral_prod_symm _ hS, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [D.ae_G_slice_integrable, D.hwg, ae_restrict_mem measurableSet_Ioc] with σ h1 h2 h3
  have := D.ibp_slice ha haδ ⟨h3.1.le, h3.2⟩ h1 (fun x hx i => h2 a ha haδ x hx i)
  simpa [S] using this

theorem energy_mollified {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2) =
      (∫ z, D.H1 a z ∂D.μP) - ∫ z, D.S a z ∂D.μP := by
  rw [D.energy_spacetime ha haδ, D.integral_H2_eq ha haδ]
  ring

end Data

end PDE.Parabolic.Energy
