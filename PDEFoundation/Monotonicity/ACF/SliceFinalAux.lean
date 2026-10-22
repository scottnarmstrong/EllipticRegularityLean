module

public import PDEFoundation.Monotonicity.ACF.SliceTruncRayleigh

/-!
# ACF-S2: auxiliary slice lemmas for the limit `δ → 0`
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Dominated convergence for slice integrals at a fixed radius. -/
theorem tendsto_sliceIntegral_of_dominated {Gk : ℕ → Vec d → ℝ} {G H : Vec d → ℝ} {r : ℝ}
    (hH : SliceIntegrable H r) (hm : ∀ k, SliceIntegrable (Gk k) r)
    (hb : ∀ k x, |Gk k x| ≤ H x) (hl : ∀ x, Tendsto (fun k => Gk k x) atTop (𝓝 (G x))) :
    Tendsto (fun k => sliceIntegral (Gk k) r) atTop (𝓝 (sliceIntegral G r)) := by
  simp only [sliceIntegral_eq]
  refine tendsto_integral_of_dominated_convergence
    (fun ω : Metric.sphere (0 : HilbertVec d) 1 => H (r • (ω : HilbertVec d).toVec))
    (fun k => (hm k).aestronglyMeasurable) hH (fun k => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => hl _)
  rw [Real.norm_eq_abs]
  exact hb k _

/-- A function that vanishes a.e. has vanishing, integrable slices for a.e. radius. -/
theorem ae_sliceIntegral_eq_zero [NeZero d] {G : Vec d → ℝ} (hG : G =ᵐ[volume] 0) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), SliceIntegrable G r ∧ sliceIntegral G r = 0 := by
  have hGi : Integrable G := (integrable_zero _ _ _).congr hG.symm
  obtain ⟨hae, -, -⟩ := polar_slices hGi
  have hAi : Integrable (fun x => |G x|) := hGi.abs
  obtain ⟨-, hint, heq⟩ := polar_slices hAi
  have h0 : ∫ x, |G x| = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [hG] with x hx
    simp [hx]
  rw [h0] at heq
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => r ^ (d - 1) * sliceIntegral
      (fun x => |G x|) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (pow_nonneg (le_of_lt hr) _) (sliceIntegral_nonneg (fun x => abs_nonneg _) r)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 heq.symm
  filter_upwards [hae, hz, ae_restrict_mem measurableSet_Ioi] with r h1 h2 hr
  refine ⟨h1, ?_⟩
  have h3 : sliceIntegral (fun x => |G x|) r = 0 := by
    have := h2
    simp only [Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_pos hr _).ne'
    · exact h
  exact abs_nonpos_iff.1 ((abs_sliceIntegral_le G r).trans h3.le)

end

end PDE
