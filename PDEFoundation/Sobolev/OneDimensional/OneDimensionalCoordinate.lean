module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import PDEFoundation.Measure.OneDimensionalCoordinate

/-!
# One-dimensional `MemLp` transport

This Sobolev-layer bridge records exact `MemLp` transport between scalar
Lebesgue measure on an open interval and the corresponding native `Vec 1`
axis box.  Its only change of variables is the volume-preserving coordinate
equivalence from `Measure.OneDimensionalCoordinate`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Exact `MemLp` transport from a scalar open interval to its native
one-coordinate axis box.  The exponent is arbitrary, including `⊤`. -/
theorem memLp_liftOneDimensional_iff_memLp_Ioo
    {p : ℝ≥0∞} {f : ℝ → ℝ} (a b : ℝ) :
    MemLp (liftOneDimensional f) p
      (volume.restrict (oneDimensionalAxisBox a b)) ↔
      MemLp f p (volume.restrict (Ioo a b)) := by
  rw [← vecOneEquivReal_preimage_Ioo a b]
  let hpres := volumePreserving_vecOneEquivReal.restrict_preimage_emb
    vecOneEquivReal.measurableEmbedding (Ioo a b)
  have hmap : Measure.map vecOneEquivReal
      (volume.restrict (vecOneEquivReal ⁻¹' Ioo a b)) =
        volume.restrict (Ioo a b) := hpres.map_eq
  rw [← hmap]
  simpa only [Function.comp_apply, vecOneEquivReal_apply, liftOneDimensional] using!
    (vecOneEquivReal.measurableEmbedding.memLp_map_measure_iff
      (g := f) (p := p) (μ := volume.restrict (vecOneEquivReal ⁻¹' Ioo a b))).symm

/-- Exact transport of the extended `Lᵖ` seminorm between a scalar open
interval and its native one-coordinate axis box. -/
theorem eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo
    {p : ℝ≥0∞} {f : ℝ → ℝ} (a b : ℝ) :
    eLpNorm (liftOneDimensional f) p
        (volume.restrict (oneDimensionalAxisBox a b)) =
      eLpNorm f p (volume.restrict (Ioo a b)) := by
  rw [← vecOneEquivReal_preimage_Ioo a b]
  let hpres := volumePreserving_vecOneEquivReal.restrict_preimage_emb
    vecOneEquivReal.measurableEmbedding (Ioo a b)
  have hmap : Measure.map vecOneEquivReal
      (volume.restrict (vecOneEquivReal ⁻¹' Ioo a b)) =
        volume.restrict (Ioo a b) := hpres.map_eq
  rw [← hmap]
  simpa only [Function.comp_apply, vecOneEquivReal_apply,
    liftOneDimensional] using!
      (vecOneEquivReal.measurableEmbedding.eLpNorm_map_measure
        (g := f) (p := p)
        (μ := volume.restrict
          (vecOneEquivReal ⁻¹' Ioo a b))).symm

/-- The `p = 2` specialization of the exact one-dimensional transport. -/
theorem memLp_two_liftOneDimensional_iff_memLp_two_Ioo
    {f : ℝ → ℝ} (a b : ℝ) :
    MemLp (liftOneDimensional f) 2
      (volume.restrict (oneDimensionalAxisBox a b)) ↔
      MemLp f 2 (volume.restrict (Ioo a b)) :=
  memLp_liftOneDimensional_iff_memLp_Ioo (p := 2) a b

/-- Exact transport of almost-everywhere equality between a scalar open
interval and its native one-coordinate axis box. -/
theorem aeEq_liftOneDimensional_iff_aeEq_Ioo
    {f g : ℝ → ℝ} (a b : ℝ) :
    liftOneDimensional f =ᵐ[
        volume.restrict (oneDimensionalAxisBox a b)]
      liftOneDimensional g ↔
      f =ᵐ[volume.restrict (Ioo a b)] g := by
  rw [← vecOneEquivReal_preimage_Ioo a b]
  let hpres := volumePreserving_vecOneEquivReal.restrict_preimage_emb
    vecOneEquivReal.measurableEmbedding (Ioo a b)
  have hmap : Measure.map vecOneEquivReal
      (volume.restrict (vecOneEquivReal ⁻¹' Ioo a b)) =
        volume.restrict (Ioo a b) := hpres.map_eq
  rw [← hmap]
  change
    (∀ᵐ x ∂volume.restrict (vecOneEquivReal ⁻¹' Ioo a b),
        f (vecOneEquivReal x) = g (vecOneEquivReal x)) ↔
      ∀ᵐ t ∂Measure.map vecOneEquivReal
          (volume.restrict (vecOneEquivReal ⁻¹' Ioo a b)),
        f t = g t
  exact
    (vecOneEquivReal.measurableEmbedding.ae_map_iff
      (μ := volume.restrict (vecOneEquivReal ⁻¹' Ioo a b))
      (p := fun t => f t = g t)).symm

end

end PDE
