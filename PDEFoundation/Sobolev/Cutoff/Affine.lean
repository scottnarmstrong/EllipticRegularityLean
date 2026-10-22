module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Sobolev.Cutoff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Affine transport of quantitative smooth cutoffs

Translation preserves the gradient constant of a quantitative smooth cutoff.
Pullback by a positive dilation of factor `r` divides that constant by `r`.
Both constructions transport the prescribed sets and topological support
exactly.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace QuantitativeSmoothCutoff

variable {d : ℕ}
variable {inner outer : Set (Vec d)}
variable {K : ℝ}

private theorem classicalGradient_comp_subRight
    (f : Vec d → ℝ) (z x : Vec d) :
    classicalGradient (fun y => f (y - z)) x =
      classicalGradient f (x - z) := by
  ext i
  have hderiv :
      fderiv ℝ (fun y : Vec d => f (y - z)) x =
        fderiv ℝ f (x - z) := by
    simpa only [sub_eq_add_neg] using
      (fderiv_comp_add_right (𝕜 := ℝ) (f := f)
        (x := x) (-z))
  simp only [classicalGradient_apply, hderiv]

private theorem classicalGradient_comp_smul
    (f : Vec d → ℝ) (c : ℝ) (x : Vec d) :
    classicalGradient (fun y => f (c • y)) x =
      c • classicalGradient f (c • x) := by
  ext i
  have hderiv :
      fderiv ℝ (fun y : Vec d => f (c • y)) x =
        c • fderiv ℝ f (c • x) := by
    simpa only using
      (fderiv_comp_smul (𝕜 := ℝ) (f := f) (x := x) c)
  simpa only [classicalGradient_apply, Pi.smul_apply,
    smul_eq_mul] using!
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i))
      hderiv

/-- Translate a cutoff by `z`, preserving its quantitative gradient bound. -/
noncomputable def translate
    (η : QuantitativeSmoothCutoff inner outer K)
    (z : Vec d) :
    QuantitativeSmoothCutoff
      (translateSet z inner) (translateSet z outer) K where
  toFun := fun x => η.toFun (x - z)
  smooth := by
    exact η.smooth.comp (contDiff_id.sub contDiff_const)
  hasCompactSupport := by
    show HasCompactSupport
      (η.toFun ∘ Homeomorph.subRight z)
    exact η.hasCompactSupport.comp_homeomorph
      (Homeomorph.subRight z)
  tsupport_subset := by
    rw [show (fun x => η.toFun (x - z)) =
      η.toFun ∘ Homeomorph.subRight z by rfl,
      tsupport_comp_eq_preimage]
    intro x hx
    exact (mem_translateSet_iff_sub_mem).2
      (η.tsupport_subset hx)
  nonneg := fun x => η.nonneg (x - z)
  le_one := fun x => η.le_one (x - z)
  eq_one_on_inner := by
    intro x hx
    exact η.eq_one_on_inner (x - z)
      ((mem_translateSet_iff_sub_mem).mp hx)
  gradient_bound := by
    intro x
    rw [classicalGradient_comp_subRight]
    exact η.gradient_bound (x - z)

@[simp]
theorem translate_toFun
    (η : QuantitativeSmoothCutoff inner outer K)
    (z x : Vec d) :
    (η.translate z).toFun x = η.toFun (x - z) :=
  rfl

@[simp]
theorem translate_classicalGradient
    (η : QuantitativeSmoothCutoff inner outer K)
    (z x : Vec d) :
    classicalGradient (η.translate z).toFun x =
      classicalGradient η.toFun (x - z) :=
  classicalGradient_comp_subRight η.toFun z x

@[simp]
theorem translate_tsupport
    (η : QuantitativeSmoothCutoff inner outer K)
    (z : Vec d) :
    tsupport (η.translate z).toFun =
      translateSet z (tsupport η.toFun) := by
  rw [show (η.translate z).toFun =
    η.toFun ∘ Homeomorph.subRight z by rfl,
    tsupport_comp_eq_preimage]
  exact preimage_subRight_eq_translateSet z (tsupport η.toFun)

/-- Pull a cutoff back by inverse positive dilation.

The transformed cutoff lives between `r • inner` and `r • outer`; its
pointwise Euclidean gradient bound is `K / r`. -/
noncomputable def dilate_of_pos
    (η : QuantitativeSmoothCutoff inner outer K)
    {r : ℝ} (hr : 0 < r) :
    QuantitativeSmoothCutoff (r • inner) (r • outer) (K / r) where
  toFun := fun x => η.toFun (r⁻¹ • x)
  smooth := by
    exact η.smooth.comp (contDiff_const_smul r⁻¹)
  hasCompactSupport := by
    exact η.hasCompactSupport.comp_smul
      (inv_ne_zero hr.ne')
  tsupport_subset := by
    rw [show (fun x => η.toFun (r⁻¹ • x)) =
      η.toFun ∘ Homeomorph.smulOfNeZero r⁻¹
        (inv_ne_zero hr.ne') by rfl,
      tsupport_comp_eq_preimage]
    intro x hx
    exact (Set.mem_smul_set_iff_inv_smul_mem₀
      hr.ne' outer x).2 (η.tsupport_subset hx)
  nonneg := fun x => η.nonneg (r⁻¹ • x)
  le_one := fun x => η.le_one (r⁻¹ • x)
  eq_one_on_inner := by
    intro x hx
    exact η.eq_one_on_inner (r⁻¹ • x)
      ((Set.mem_smul_set_iff_inv_smul_mem₀
        hr.ne' inner x).mp hx)
  gradient_bound := by
    intro x
    rw [classicalGradient_comp_smul,
      vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹ * vecEuclideanNorm
          (classicalGradient η.toFun (r⁻¹ • x)) ≤
          r⁻¹ * K :=
        mul_le_mul_of_nonneg_left
          (η.gradient_bound (r⁻¹ • x))
          (inv_nonneg.mpr hr.le)
      _ = K / r := by
        rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem dilate_of_pos_toFun
    (η : QuantitativeSmoothCutoff inner outer K)
    {r : ℝ} (hr : 0 < r) (x : Vec d) :
    (η.dilate_of_pos hr).toFun x =
      η.toFun (r⁻¹ • x) :=
  rfl

@[simp]
theorem dilate_of_pos_classicalGradient
    (η : QuantitativeSmoothCutoff inner outer K)
    {r : ℝ} (hr : 0 < r) (x : Vec d) :
    classicalGradient (η.dilate_of_pos hr).toFun x =
      r⁻¹ • classicalGradient η.toFun (r⁻¹ • x) :=
  classicalGradient_comp_smul η.toFun r⁻¹ x

@[simp]
theorem dilate_of_pos_tsupport
    (η : QuantitativeSmoothCutoff inner outer K)
    {r : ℝ} (hr : 0 < r) :
    tsupport (η.dilate_of_pos hr).toFun =
      r • tsupport η.toFun := by
  rw [show (η.dilate_of_pos hr).toFun =
    η.toFun ∘ Homeomorph.smulOfNeZero r⁻¹
      (inv_ne_zero hr.ne') by rfl,
    tsupport_comp_eq_preimage]
  exact Set.preimage_smul_inv₀ hr.ne' (tsupport η.toFun)

end QuantitativeSmoothCutoff

end PDE
