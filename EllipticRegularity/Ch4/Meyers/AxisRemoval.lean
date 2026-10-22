module

public import EllipticRegularity.Ch4.Meyers.AxisError
public import PDEFoundation.Sobolev.ClassicalOnOpenWeakGradient

/-!
# Removability of the codimension-two set `{s = 0}` for weak gradients

If `f` and `G` are in `L²(U)`, `f` is `C¹` on `U \ {s = 0}` with classical gradient `G` there,
and `s = ∑ w_j x_j²` involves at least two coordinates with weight one, then `G` is the weak
gradient of `f` on all of `U`.  The proof cuts off with `axisCutoff`; the error term is handled
by `tendsto_lintegral_axis_error`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Meyers

open MeasureTheory Set Filter

variable {d : ℕ} {w : Fin d → ℝ}

/-- The singular set `{s = 0}` is null when two coordinates carry weight one. -/
theorem volume_axisSq_eq_zero (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 : Fin d} (h0 : w i0 = 1) :
    volume {x : Vec d | axisSq w x = 0} = 0 := by
  refine measure_mono_null ?_ (Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i0 0)
  intro x hx
  have h1 := sq_le_axisSq hw x h0
  have hx' : axisSq w x = 0 := hx
  have : x i0 ^ 2 = 0 := le_antisymm (hx' ▸ h1) (sq_nonneg _)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

theorem ae_axisSq_pos (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 : Fin d} (h0 : w i0 = 1)
    (U : Set (Vec d)) : ∀ᵐ x ∂(volume.restrict U), 0 < axisSq w x := by
  apply ae_restrict_of_ae
  have := measure_eq_zero_iff_ae_notMem.mp (volume_axisSq_eq_zero hw h0)
  filter_upwards [this] with x hx
  exact lt_of_le_of_ne (axisSq_nonneg hw x) (fun h => hx h.symm)

/-- Bochner version of the cutoff error estimate. -/
theorem tendsto_integral_axis_error (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 i1 : Fin d}
    (hi : i0 ≠ i1) (h0 : w i0 = 1) (h1 : w i1 = 1) {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (φ : WeakTestFunction U) (i : Fin d)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U,
      f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)) atTop (𝓝 0) := by
  have hL := tendsto_lintegral_axis_error hw hi h0 h1 hf φ i ε hε hε0
  have hLreal : Tendsto (fun n => (∫⁻ x in U,
      ENNReal.ofReal |f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)|).toReal)
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_apply] using!
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _ hLreal
  filter_upwards with n
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_lintegral_norm (μ := volume.restrict U)
      (fun x => f x * φ x * fderiv ℝ (axisCutoff w (ε n)) x (basisVec i)))

theorem tendsto_integral_mul_axisCutoff (hw : ∀ i, w i = 0 ∨ w i = 1) {i0 : Fin d}
    (h0 : w i0 = 1) {U : Set (Vec d)} {h : Vec d → ℝ}
    (hh : Integrable h (volume.restrict U)) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, h x * axisCutoff w (ε n) x) atTop (𝓝 (∫ x in U, h x)) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => h x * axisCutoff w (ε n) x)
      (volume.restrict U) :=
    hh.aestronglyMeasurable.mul (axisCutoff_smooth w (ε n)).continuous.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂(volume.restrict U), ‖h x * axisCutoff w (ε n) x‖ ≤ ‖h x‖ := by
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs (axisCutoff w (ε n) x),
      abs_of_nonneg (axisCutoff_nonneg w _ x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (axisCutoff_le_one w _ x)
  have hpoint : ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => h x * axisCutoff w (ε n) x) atTop (𝓝 (h x)) := by
    filter_upwards [ae_axisSq_pos hw h0 U] with x hx
    simpa using (axisCutoff_tendsto_one hx ε hε hε0).const_mul (h x)
  exact tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) hmeas hh.norm hbound hpoint

end PDE.Ch4Meyers
