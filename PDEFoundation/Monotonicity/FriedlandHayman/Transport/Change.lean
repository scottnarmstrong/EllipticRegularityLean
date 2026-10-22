module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Contraction
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Friedland--Hayman: change of variables along the transport map

For `D ≥ 3` the map `tmap D` is a strictly decreasing `C¹` bijection of `ℝ` onto `(0, π)`, so
`∫_{(0,π)} H sinW = (zTot / gTot) ∫_ℝ (H ∘ tmap) gaussW`, and the preimage of a null set is null.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PDE.FHLane

namespace Transp

noncomputable section

theorem continuous_tmap (D : ℕ) : Continuous (tmap D) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_tmap D s).continuousAt

theorem continuous_dtmap (D : ℕ) : Continuous (dtmap D) := by
  unfold dtmap
  refine (continuous_const.mul continuous_gaussW).div ((continuous_sinW D).comp (continuous_tmap D))
    fun s => (sinW_pos (D := D) (tmap_mem D s)).ne'

theorem tmap_image (D : ℕ) : tmap D '' Set.univ = Set.Ioo 0 Real.pi := by
  ext φ
  constructor
  · rintro ⟨s, -, rfl⟩
    exact tmap_mem D s
  · intro hφ
    obtain ⟨s, hs⟩ := exists_tmap_eq D hφ
    exact ⟨s, mem_univ _, hs⟩

theorem integral_tmap {D : ℕ} (hD : 3 ≤ D) (H : ℝ → ℝ) :
    ∫ φ in Set.Ioo 0 Real.pi, H φ * sinW D φ =
      (zTot D / gTot) * ∫ s, H (tmap D s) * gaussW s := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := tmap D) (f' := dtmap D)
    MeasurableSet.univ (fun x _ => (hasDerivAt_tmap D x).hasDerivWithinAt)
    (tmap_strictAnti D).injective.injOn (fun φ => H φ * sinW D φ)
  rw [tmap_image, Measure.restrict_univ] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [smul_eq_mul]
  have hz := (sinW_pos (D := D) (tmap_mem D s)).ne'
  have hn := dtmap_neg hD s
  rw [abs_of_neg hn]
  unfold dtmap
  field_simp

theorem ae_tmap_not_mem {D : ℕ} (hD : 3 ≤ D) {N : Set ℝ} (hN : volume N = 0) :
    ∀ᵐ s, tmap D s ∉ N := by
  set N' := toMeasurable volume N with hN'
  have hm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have h0 : volume N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := tmap D) (f' := dtmap D)
    MeasurableSet.univ (fun x _ => (hasDerivAt_tmap D x).hasDerivWithinAt)
    (tmap_strictAnti D).injective.injOn (N'.indicator 1)
  have hl : ∫⁻ x in tmap D '' Set.univ, N'.indicator 1 x = 0 := by
    rw [lintegral_indicator_one hm]
    exact le_antisymm ((Measure.restrict_le_self N').trans_eq h0) zero_le
  rw [hl, Measure.restrict_univ] at h
  have hmeas : Measurable fun x => ENNReal.ofReal |dtmap D x| * N'.indicator (1 : ℝ → ENNReal)
      (tmap D x) :=
    (ENNReal.measurable_ofReal.comp (continuous_dtmap D).abs.measurable).mul
      ((measurable_one.indicator hm).comp (continuous_tmap D).measurable)
  have := (lintegral_eq_zero_iff hmeas).1 h.symm
  filter_upwards [this] with s hs hsN
  have hsN' : tmap D s ∈ N' := subset_toMeasurable _ _ hsN
  simp only [Pi.zero_apply, indicator_of_mem hsN', Pi.one_apply, mul_one,
    ENNReal.ofReal_eq_zero] at hs
  have := dtmap_neg hD s
  have : 0 < |dtmap D s| := abs_pos.2 this.ne
  linarith

end

end Transp

end PDE.FHLane
