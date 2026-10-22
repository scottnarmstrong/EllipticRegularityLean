module

public import PDEFoundation.Measure.NormalizedLp

/-!
# Dilation transport for restricted `L^p` norms

This file proves exact change-of-variables formulas under positive scalar
dilation on native project vectors. Restricted volume acquires the explicit
Jacobian factor `r ^ d`, whereas normalized restricted volume is preserved
exactly.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE

open MeasureTheory

/-- Pullback by inverse positive dilation sends restricted volume on `r • U`
to `r ^ d` times restricted volume on `U`. -/
theorem measurePreserving_inv_smul_restrict_smul_set
    {d : ℕ} {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => r⁻¹ • x)
      (volumeOn (r • U))
      (ENNReal.ofReal (r ^ d) • volumeOn U) := by
  have hbase :
      MeasurePreserving (fun x : Vec d => r⁻¹ • x)
        (volume : Measure (Vec d))
        (ENNReal.ofReal (r ^ d) • (volume : Measure (Vec d))) := by
    refine ⟨measurable_const_smul _, ?_⟩
    simpa [Vec, abs_of_pos (pow_pos hr d)] using
      (Measure.map_addHaar_smul (volume : Measure (Vec d))
        (inv_ne_zero hr.ne'))
  have hemb : MeasurableEmbedding (fun x : Vec d => r⁻¹ • x) := by
    let u : ℝˣ := (isUnit_iff_ne_zero.2 (inv_ne_zero hr.ne')).unit
    have hu : (u : ℝ) = r⁻¹ :=
      (isUnit_iff_ne_zero.2 (inv_ne_zero hr.ne')).unit_spec
    simpa [hu] using!
      (Homeomorph.smul u : Vec d ≃ₜ Vec d).measurableEmbedding
  simpa only [volumeOn, Set.preimage_smul_inv₀ hr.ne' U,
    Measure.restrict_smul] using
    hbase.restrict_preimage_emb hemb U

/-- Exact restricted `L^p` scaling under positive dilation.

The statement is valid for every extended exponent, including `0` and `∞`,
with Mathlib's conventions for `eLpNorm`.
-/
theorem eLpNormOn_comp_inv_smul_smul_set
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) (p : ℝ≥0∞)
    (f : Vec d → E) (hf : AEStronglyMeasurable f (volumeOn U)) :
    eLpNormOn (r • U) p (fun x => f (r⁻¹ • x)) =
      ENNReal.ofReal (r ^ d) ^ (1 / p).toReal *
        eLpNormOn U p f := by
  let c : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  have hc : c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (pow_pos hr d))
  calc
    eLpNormOn (r • U) p (fun x => f (r⁻¹ • x)) =
        eLpNorm f p (c • volumeOn U) := by
      simpa only [eLpNormOn, Function.comp_apply, c] using!
        eLpNorm_comp_measurePreserving (hf.smul_measure c)
          (measurePreserving_inv_smul_restrict_smul_set hr U)
    _ = c ^ (1 / p).toReal * eLpNormOn U p f := by
      rw [eLpNorm_smul_measure_of_ne_zero hc]
      rfl
    _ = ENNReal.ofReal (r ^ d) ^ (1 / p).toReal *
        eLpNormOn U p f := rfl

/-- Exact restricted `L^p` scaling under positive dilation, including a
constant amplitude factor. -/
theorem eLpNormOn_const_smul_comp_inv_smul_smul_set
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (a : ℝ) (U : Set (Vec d)) (p : ℝ≥0∞)
    (f : Vec d → E) (hf : AEStronglyMeasurable f (volumeOn U)) :
    eLpNormOn (r • U) p (fun x => a • f (r⁻¹ • x)) =
      ‖a‖ₑ * ENNReal.ofReal (r ^ d) ^ (1 / p).toReal *
        eLpNormOn U p f := by
  calc
    eLpNormOn (r • U) p (fun x => a • f (r⁻¹ • x)) =
        ENNReal.ofReal (r ^ d) ^ (1 / p).toReal *
          eLpNormOn U p (a • f) := by
      simpa only [Pi.smul_apply] using
        eLpNormOn_comp_inv_smul_smul_set hr U p (a • f)
          (hf.const_smul a)
    _ = ENNReal.ofReal (r ^ d) ^ (1 / p).toReal *
        (‖a‖ₑ * eLpNormOn U p f) := by
      simpa only [eLpNormOn] using
        congrArg
          (fun q => ENNReal.ofReal (r ^ d) ^ (1 / p).toReal * q)
          (eLpNorm_const_smul a f p (volumeOn U))
    _ = ‖a‖ₑ * ENNReal.ofReal (r ^ d) ^ (1 / p).toReal *
        eLpNormOn U p f := by
      ac_rfl

/-- Pullback by inverse positive dilation preserves normalized restricted
volume exactly. The total definition of `normalizedVolumeOn` makes this valid
without separate assumptions on the volume of `U`. -/
theorem measurePreserving_inv_smul_normalizedVolumeOn_smul_set
    {d : ℕ} {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => r⁻¹ • x)
      (normalizedVolumeOn (r • U)) (normalizedVolumeOn U) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  have hc : c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.2 (pow_pos hr d))
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcoef : (c * volume U)⁻¹ * c = (volume U)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hcTop)]
    calc
      (c⁻¹ * (volume U)⁻¹) * c =
          (c⁻¹ * c) * (volume U)⁻¹ := by
        ac_rfl
      _ = (volume U)⁻¹ := by
        rw [ENNReal.inv_mul_cancel hc hcTop, one_mul]
  refine ⟨measurable_const_smul _, ?_⟩
  rw [normalizedVolumeOn, Measure.map_smul _ (measurable_const_smul _).aemeasurable,
    (measurePreserving_inv_smul_restrict_smul_set hr U).map_eq,
    volume_smul_set_of_nonneg hr.le U]
  change (c * volume U)⁻¹ • (c • volumeOn U) =
    (volume U)⁻¹ • volumeOn U
  rw [smul_smul, hcoef]

/-- The normalized `L^p` mean norm is exactly invariant under positive
dilation. -/
theorem eLpMeanNormOn_comp_inv_smul_smul_set
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) (p : ℝ≥0∞)
    (f : Vec d → E)
    (hf : AEStronglyMeasurable f (normalizedVolumeOn U)) :
    eLpMeanNormOn (r • U) p (fun x => f (r⁻¹ • x)) =
      eLpMeanNormOn U p f := by
  simpa only [eLpMeanNormOn, Function.comp_apply] using!
    eLpNorm_comp_measurePreserving hf
      (measurePreserving_inv_smul_normalizedVolumeOn_smul_set hr U)

/-- The normalized `L^p` mean norm under positive dilation, including a
constant amplitude factor. -/
theorem eLpMeanNormOn_const_smul_comp_inv_smul_smul_set
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (a : ℝ) (U : Set (Vec d)) (p : ℝ≥0∞)
    (f : Vec d → E)
    (hf : AEStronglyMeasurable f (normalizedVolumeOn U)) :
    eLpMeanNormOn (r • U) p (fun x => a • f (r⁻¹ • x)) =
      ‖a‖ₑ * eLpMeanNormOn U p f := by
  calc
    eLpMeanNormOn (r • U) p (fun x => a • f (r⁻¹ • x)) =
        eLpMeanNormOn U p (a • f) := by
      simpa only [Pi.smul_apply] using
        eLpMeanNormOn_comp_inv_smul_smul_set hr U p (a • f)
          (hf.const_smul a)
    _ = ‖a‖ₑ * eLpMeanNormOn U p f := by
      simpa only [eLpMeanNormOn] using
        (eLpNorm_const_smul a f p (normalizedVolumeOn U))

end PDE
