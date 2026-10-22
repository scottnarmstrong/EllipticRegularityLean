module

public import EllipticRegularity.Parabolic.SliceEstimate.TimeEnergyCore

/-!
# Bounding the mollified time-energy estimate by `G` and `∫ φ⁴ B`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

namespace EData

variable (D : EData d)

theorem integrable_r0 {ε : ℝ} : Integrable (D.r0 ε) (D.μ D.q) := by
  have hW := fun i => (D.memLp_W le_rfl i).1
  have hZ0 := fun i => (D.memLp_W le_rfl i).2
  obtain ⟨M1, hM1⟩ := D.ae_bound_weight (D.continuous_w3 ε) (le_refl D.q)
  obtain ⟨M2, hM2⟩ := D.ae_bound_weight (D.continuous_w2 ε) (le_refl D.q)
  have i3 := D.integrable_qf (t := D.q) (D.continuous_w3 ε).aestronglyMeasurable hM1 hW hW
  have i4 := D.integrable_qf (t := D.q) (D.continuous_w2 ε).aestronglyMeasurable hM2 hZ0 hZ0
  exact i3.add i4

theorem integrable_Au : Integrable (fun z => qf (D.A z.1) (D.Wv z) (D.Wv z)) (D.μ D.q) := by
  have hW := fun i => (D.memLp_W le_rfl i).1
  obtain ⟨M, hM⟩ := D.ae_bound_weight (continuous_const (y := (1 : ℝ))) (le_refl D.q)
  have := D.integrable_qf (t := D.q) (ω := fun _ => 1) continuous_const.aestronglyMeasurable hM hW hW
  simp only [one_mul] at this
  exact this

theorem integrable_Bv : Integrable (fun z => D.φ z ^ 4 * qf (D.A z.1) (D.Zv z) (D.Zv z))
    (D.μ D.q) := by
  have hZ0 := fun i => (D.memLp_W le_rfl i).2
  obtain ⟨M, hM⟩ := D.ae_bound_weight (D.continuous_phi.pow 4) (le_refl D.q)
  exact D.integrable_qf (t := D.q) (D.continuous_phi.pow 4).aestronglyMeasurable hM hZ0 hZ0

/-- The mollified time-energy estimate, bounded by `G` and `∫ φ⁴ B`. -/
theorem time_energy_bound {ε : ℝ} (hε : 0 < ε) {c1 : ℝ}
    (h1 : ∀ᵐ z ∂(D.μ D.q), |parTimeDeriv D.φ z| ≤ c1)
    (hφ1 : ∀ᵐ z ∂(D.μ D.q), |D.φ z| ≤ 1) :
    ∀ᵐ t ∂(volume.restrict (Ioc D.p D.q)), D.Eu t ≤
      (4 * c1 + ε⁻¹) * (∫ z, {z : Vec d × ℝ | D.φ z ≠ 0}.indicator
          (fun z => qf (D.A z.1) (D.Wv z) (D.Wv z)) z ∂(D.μ D.q)) +
        ε * ∫ z, D.φ z ^ 4 * qf (D.A z.1) (D.Zv z) (D.Zv z) ∂(D.μ D.q) := by
  filter_upwards [D.time_energy hε] with t ht
  refine ht.trans ?_
  have hmS : MeasurableSet {z : Vec d × ℝ | D.φ z ≠ 0} :=
    (isClosed_eq D.continuous_phi continuous_const).isOpen_compl.measurableSet
  have hInd : Integrable ({z : Vec d × ℝ | D.φ z ≠ 0}.indicator
      (fun z => qf (D.A z.1) (D.Wv z) (D.Wv z))) (D.μ D.q) := D.integrable_Au.indicator hmS
  have hR : Integrable (fun z => (4 * c1 + ε⁻¹) * {z : Vec d × ℝ | D.φ z ≠ 0}.indicator
      (fun z => qf (D.A z.1) (D.Wv z) (D.Wv z)) z +
        ε * (D.φ z ^ 4 * qf (D.A z.1) (D.Zv z) (D.Zv z))) (D.μ D.q) :=
    (hInd.const_mul _).add (D.integrable_Bv.const_mul _)
  have hmono : ∫ z, D.r0 ε z ∂(D.μ D.q) ≤ ∫ z, ((4 * c1 + ε⁻¹) *
      {z : Vec d × ℝ | D.φ z ≠ 0}.indicator
        (fun z => qf (D.A z.1) (D.Wv z) (D.Wv z)) z +
        ε * (D.φ z ^ 4 * qf (D.A z.1) (D.Zv z) (D.Zv z))) ∂(D.μ D.q) := by
    refine integral_mono_ae D.integrable_r0 hR ?_
    filter_upwards [h1, hφ1, D.ae_elliptic (t := D.q)] with z hz1 hz2 hz3
    have hAu := qf_self_nonneg hz3 (D.Wv z)
    unfold r0
    by_cases hφ : D.φ z = 0
    · simp [hφ]
    · have hI : {z : Vec d × ℝ | D.φ z ≠ 0}.indicator
          (fun z => qf (D.A z.1) (D.Wv z) (D.Wv z)) z = qf (D.A z.1) (D.Wv z) (D.Wv z) :=
        indicator_of_mem (show z ∈ {z : Vec d × ℝ | D.φ z ≠ 0} from hφ) _
      rw [hI]
      have hφ3 : |D.φ z| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hz2
      have hφ4 : D.φ z ^ 4 ≤ 1 := by
        have : D.φ z ^ 4 = |D.φ z| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [this]; exact pow_le_one₀ (abs_nonneg _) hz2
      have hb : 4 * |D.φ z| ^ 3 * |parTimeDeriv D.φ z| + ε⁻¹ * D.φ z ^ 4 ≤ 4 * c1 + ε⁻¹ := by
        have h5 : |D.φ z| ^ 3 * |parTimeDeriv D.φ z| ≤ c1 := by
          calc |D.φ z| ^ 3 * |parTimeDeriv D.φ z| ≤ 1 * c1 :=
                mul_le_mul hφ3 hz1 (abs_nonneg _) zero_le_one
            _ = c1 := one_mul _
        have h6 : ε⁻¹ * D.φ z ^ 4 ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left hφ4 (by positivity)
        nlinarith [h5, h6]
      have := mul_le_mul_of_nonneg_right hb hAu
      nlinarith [this]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add (hInd.const_mul _) (D.integrable_Bv.const_mul _), integral_const_mul,
    integral_const_mul]

end EData

end PDE.Parabolic.Slice
