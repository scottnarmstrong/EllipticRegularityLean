module

public import EllipticRegularity.Parabolic.Cauchy.Duality.PairIntegrable

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology

/-- Dominated convergence removes a bounded smooth spatial cutoff from an integrable
endpoint pairing. -/
theorem cauchy_duality_endpoint_cutoff_tendsto {d : ℕ} {h : Vec d → ℝ}
    (hh : Integrable h) (φ : ℕ → Vec d → ℝ)
    (hφcont : ∀ n, Continuous (φ n))
    (hφbound : ∀ n x, |φ n x| ≤ 1)
    (hφtendsto : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x : Vec d, (φ n x) ^ 2 * h x) atTop
      (𝓝 (∫ x : Vec d, h x)) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun x : Vec d => (φ n x) ^ 2 * h x) volume := by
    intro n
    exact (hφcont n).aestronglyMeasurable.pow 2 |>.mul hh.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂volume, ‖(φ n x) ^ 2 * h x‖ ≤ ‖h x‖ := by
    intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hφsq : (φ n x) ^ 2 ≤ 1 := by
      calc
        (φ n x) ^ 2 = |φ n x| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 (hφbound n x)
        _ = 1 := by norm_num
    calc
      (φ n x) ^ 2 * |h x| ≤ 1 * |h x| :=
        mul_le_mul_of_nonneg_right hφsq (abs_nonneg _)
      _ = |h x| := by ring
  have hpoint : ∀ᵐ x ∂volume, Tendsto (fun n => (φ n x) ^ 2 * h x) atTop
      (𝓝 (h x)) := by
    filter_upwards [] with x
    simpa using (hφtendsto x).pow 2 |>.mul_const (h x)
  exact tendsto_integral_of_dominated_convergence (fun x => ‖h x‖)
    hmeas hh.norm hbound hpoint

end PDE.Parabolic.Duality
