module

public import EllipticRegularity.Parabolic.Cauchy.Lions.MollifiedEnergyUniformBound

/-! # Passing cutoff energy estimates to balls -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

theorem cauchyEnergyData_ball_slice_bound
    {d : ℕ} (D : PDE.Parabolic.Energy.Data d) {B : Set (Vec d)}
    (hBmeas : MeasurableSet B) (hBsub : B ⊆ D.K)
    (hχone : ∀ x ∈ B, D.φ (x, D.t) = 1)
    {w : Vec d × ℝ → ℝ} (hrep : ∀ x, D.u (x, D.t) = w (x, D.t))
    (hphi : ∀ z, |D.φ z| ≤ 1)
    (hslice : MemLp (fun x => D.u (x, D.t)) 2 (volume.restrict D.K1))
    (hKsub : D.K ⊆ D.K1) {C : ℝ}
    (hbound : (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2) ≤ C) :
    (∫ x in B, w (x, D.t) ^ 2) ≤ C := by
  let q : Vec d → ℝ := fun x => D.φ (x, D.t) ^ 2
  have hqcont : Continuous q := by
    dsimp [q]
    exact (D.hφ.continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hqmeas : AEStronglyMeasurable q (volume.restrict D.K) :=
    hqcont.aestronglyMeasurable
  have hqbound : ∀ᵐ x ∂(volume.restrict D.K), ‖q x‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_pow]
    have h0 : 0 ≤ |D.φ (x, D.t)| := abs_nonneg _
    have h1 : |D.φ (x, D.t)| ≤ 1 := hphi (x, D.t)
    have hsquare := mul_self_le_mul_self h0 h1
    nlinarith
  have hKmeasure : volume.restrict D.K ≤ volume.restrict D.K1 :=
    Measure.restrict_mono hKsub le_rfl
  have hsq : Integrable (fun x => D.u (x, D.t) ^ 2)
      (volume.restrict D.K) := hslice.integrable_sq.mono_measure hKmeasure
  have hweight : Integrable (fun x => q x * D.u (x, D.t) ^ 2)
      (volume.restrict D.K) := hsq.bdd_mul hqmeas (c := 1) hqbound
  have hweight_nonneg : 0 ≤ᵐ[volume.restrict D.K]
      (fun x => q x * D.u (x, D.t) ^ 2) := by
    filter_upwards [] with x
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hBsubAE : B ≤ᵐ[volume] D.K :=
    ae_of_all _ fun x hx => hBsub hx
  have hmono := setIntegral_mono_set hweight hweight_nonneg hBsubAE
  have hEq : (∫ x in B, w (x, D.t) ^ 2) =
      ∫ x in B, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2 := by
    apply setIntegral_congr_fun hBmeas
    intro x hx
    change w (x, D.t) ^ 2 =
      D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2
    rw [← hrep x, hχone x hx]
    ring
  rw [hEq]
  calc
    (∫ x in B, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2) ≤
        ∫ x in D.K, D.φ (x, D.t) ^ 2 * D.u (x, D.t) ^ 2 := by
          simpa [q] using hmono
    _ ≤ C := hbound

end PDE.Parabolic.Lions
