module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Measure.DilationLp
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.WeakDerivative.Affine

/-!
# Affine transport of representative-level `W^{1,p}`

Translation acts by precomposition with `x ↦ x - z` and preserves both value
and gradient `L^p` classes exactly.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE

namespace W1pFunction

/-- Translate a representative-level Sobolev function from `U` to `z + U`. -/
noncomputable def translate {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} (u : W1pFunction U p) (z : Vec d) :
    W1pFunction (translateSet z U) p := by
  let T : Vec d → Vec d := fun x => x - z
  let hμ :=
    measurePreserving_subRight_restrict_translateSet (d := d) z U
  refine
    { toFun := fun x => u.toFun (T x)
      grad := fun x => u.grad (T x)
      memLp := ?_
      gradMemLp := ?_
      hasWeakGradient := u.hasWeakGradient.translate z }
  · show MemLpOn (translateSet z U) p (u.toFun ∘ T)
    simpa [MemLpOn, T, Function.comp] using
      u.memLp.comp_measurePreserving hμ
  · intro i
    show MemLpOn (translateSet z U) p
      ((fun x => u.grad x i) ∘ T)
    simpa [MemLpOn, T, Function.comp] using
      (u.gradMemLp i).comp_measurePreserving hμ

@[simp]
theorem translate_toFun {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} (u : W1pFunction U p) (z x : Vec d) :
    (u.translate z).toFun x = u.toFun (x - z) :=
  rfl

@[simp]
theorem translate_grad {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} (u : W1pFunction U p) (z x : Vec d) :
    (u.translate z).grad x = u.grad (x - z) :=
  rfl

theorem eLpNormOn_translate_toFun_eq {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (z : Vec d) :
    eLpNormOn (translateSet z U) p (u.translate z).toFun =
      eLpNormOn U p u.toFun :=
  eLpNormOn_comp_subRight_translateSet z U p u.toFun
    u.memLp.aestronglyMeasurable

theorem eLpNormOn_translate_grad_coord_eq {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (z : Vec d) (i : Fin d) :
    eLpNormOn (translateSet z U) p
        (fun x => (u.translate z).grad x i) =
      eLpNormOn U p (fun x => u.grad x i) := by
  simpa only [translate_grad] using
    eLpNormOn_comp_subRight_translateSet z U p
      (fun x => u.grad x i) (u.gradMemLp i).aestronglyMeasurable

/-- Push a representative-level Sobolev function from `U` to `a • U`
by the amplitude-normalized dilation

`v(x) = a * u(a⁻¹ • x)`, `Dv(x) = Du(a⁻¹ • x)`.

This convention makes the value and gradient have the same physical
dimension, and leaves the weak gradient as a plain pullback. -/
noncomputable def dilate {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) : W1pFunction (a • U) p := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have haNe : a ≠ 0 := ha.ne'
  have hmap :=
    map_smul_volumeOn_of_pos (d := d) (r := a⁻¹)
      (inv_pos.mpr ha) V
  have hpre : a⁻¹ • V = U := by
    ext x
    simp [V, haNe]
  have hTMeas :
      AEMeasurable T (volumeOn V) :=
    (measurable_const_smul a⁻¹).aemeasurable
  refine
    { toFun := fun x => a * u.toFun (T x)
      grad := fun x => u.grad (T x)
      memLp := ?_
      gradMemLp := ?_
      hasWeakGradient := u.hasWeakGradient.dilate_of_pos ha }
  · have huMap :
        MeasureTheory.MemLp u.toFun p
          (MeasureTheory.Measure.map T (volumeOn V)) := by
      rw [hmap, hpre]
      exact u.memLp.smul_measure ENNReal.ofReal_ne_top
    exact
      (MeasureTheory.MemLp.comp_of_map huMap hTMeas).const_mul a
  · intro i
    have hgradMap :
        MeasureTheory.MemLp (fun x => u.grad x i) p
          (MeasureTheory.Measure.map T (volumeOn V)) := by
      rw [hmap, hpre]
      exact (u.gradMemLp i).smul_measure ENNReal.ofReal_ne_top
    exact MeasureTheory.MemLp.comp_of_map hgradMap hTMeas

@[simp]
theorem dilate_toFun {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) (x : Vec d) :
    (u.dilate ha).toFun x = a * u.toFun (a⁻¹ • x) :=
  rfl

@[simp]
theorem dilate_grad {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) (x : Vec d) :
    (u.dilate ha).grad x = u.grad (a⁻¹ • x) :=
  rfl

/-- Exact unnormalized `L^p` scaling of the amplitude-normalized dilated
value. Both the amplitude and Jacobian factors are visible. -/
theorem eLpNormOn_dilate_toFun_eq {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) :
    eLpNormOn (a • U) p (u.dilate ha).toFun =
      ‖a‖ₑ * ENNReal.ofReal (a ^ d) ^ (1 / p).toReal *
        eLpNormOn U p u.toFun := by
  simpa only [dilate_toFun, smul_eq_mul] using!
    eLpNormOn_const_smul_comp_inv_smul_smul_set
      ha a U p u.toFun u.memLp.aestronglyMeasurable

/-- Exact unnormalized `L^p` scaling of each gradient coordinate under the
amplitude-normalized dilation. -/
theorem eLpNormOn_dilate_grad_coord_eq {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞} {a : ℝ}
    (ha : 0 < a) (u : W1pFunction U p) (i : Fin d) :
    eLpNormOn (a • U) p
        (fun x => (u.dilate ha).grad x i) =
      ENNReal.ofReal (a ^ d) ^ (1 / p).toReal *
        eLpNormOn U p (fun x => u.grad x i) := by
  simpa only [dilate_grad] using
    eLpNormOn_comp_inv_smul_smul_set ha U p
      (fun x => u.grad x i)
      (u.gradMemLp i).aestronglyMeasurable

/-- Exact normalized `L^p` scaling of the amplitude-normalized dilated value:
normalizing the domain removes the Jacobian factor. -/
theorem eLpMeanNormOn_dilate_toFun_eq {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞} {a : ℝ}
    (ha : 0 < a) (u : W1pFunction U p) :
    eLpMeanNormOn (a • U) p (u.dilate ha).toFun =
      ‖a‖ₑ * eLpMeanNormOn U p u.toFun := by
  have huMeas :
      MeasureTheory.AEStronglyMeasurable u.toFun
        (normalizedVolumeOn U) := by
    simpa only [normalizedVolumeOn] using
      u.memLp.aestronglyMeasurable.smul_measure
        ((MeasureTheory.volume U)⁻¹)
  simpa only [dilate_toFun, smul_eq_mul] using!
    eLpMeanNormOn_const_smul_comp_inv_smul_smul_set
      ha a U p u.toFun huMeas

/-- Each gradient coordinate has exactly invariant normalized `L^p` norm
under the amplitude-normalized dilation. -/
theorem eLpMeanNormOn_dilate_grad_coord_eq {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞} {a : ℝ}
    (ha : 0 < a) (u : W1pFunction U p) (i : Fin d) :
    eLpMeanNormOn (a • U) p
        (fun x => (u.dilate ha).grad x i) =
      eLpMeanNormOn U p (fun x => u.grad x i) := by
  have hgradMeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => u.grad x i) (normalizedVolumeOn U) := by
    simpa only [normalizedVolumeOn] using
      (u.gradMemLp i).aestronglyMeasurable.smul_measure
        ((MeasureTheory.volume U)⁻¹)
  simpa only [dilate_grad] using
    eLpMeanNormOn_comp_inv_smul_smul_set
      ha U p (fun x => u.grad x i) hgradMeas

end W1pFunction

end PDE
