module

public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Sobolev.Cutoff.Basic
public import PDEFoundation.Sobolev.Cutoff.Profile
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Smooth cutoffs in planar axis boxes

This module gives a native-`Vec 2` product cutoff for an open axis box. The
transition begins at a half-collar of width `δ / 2`, so its topological support
is genuinely contained in the open box, while it is identically one on the
closed `δ`-inset. Each coordinate derivative is bounded by `32 / δ`, and the
native Euclidean gradient is bounded by `64 / δ`.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE

/-- Smooth transition from zero near the lower endpoint to one after a
collar of width `δ`. -/
def axisBoxLowerTransition (a δ : ℝ) (t : ℝ) : ℝ :=
  smoothTransitionProfile ((t - a) / (δ / 2) - 1)

/-- Smooth transition from one before the upper collar to zero near the upper
endpoint. -/
def axisBoxUpperTransition (b δ : ℝ) (t : ℝ) : ℝ :=
  smoothTransitionProfile ((b - t) / (δ / 2) - 1)

/-- The product cutoff in the planar open box `(a,b) × (c,d)`. -/
def axisBoxInteriorCutoff (a b c d δ : ℝ) (x : Vec 2) : ℝ :=
  axisBoxLowerTransition a δ (x 0) *
    axisBoxUpperTransition b δ (x 0) *
      axisBoxLowerTransition c δ (x 1) *
        axisBoxUpperTransition d δ (x 1)

/-- The closed box obtained by removing a collar of width `δ` on each side. -/
def axisBoxInteriorInset (a b c d δ : ℝ) : Set (Vec 2) :=
  Set.pi Set.univ fun i =>
    if i = 0 then Set.Icc (a + δ) (b - δ) else Set.Icc (c + δ) (d - δ)

private theorem axisBoxLowerTransition_smooth (a δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (axisBoxLowerTransition a δ) := by
  exact smoothTransitionProfile.smooth.comp
    (((contDiff_id.sub contDiff_const).div_const _).sub contDiff_const)

private theorem axisBoxUpperTransition_smooth (b δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (axisBoxUpperTransition b δ) := by
  exact smoothTransitionProfile.smooth.comp
    (((contDiff_const.sub contDiff_id).div_const _).sub contDiff_const)

/-- The axis-box cutoff is smooth to every order. -/
theorem axisBoxInteriorCutoff_smooth (a b c d δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (axisBoxInteriorCutoff a b c d δ) := by
  unfold axisBoxInteriorCutoff
  have hL0 := (axisBoxLowerTransition_smooth a δ).comp
    (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hU0 := (axisBoxUpperTransition_smooth b δ).comp
    (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hL1 := (axisBoxLowerTransition_smooth c δ).comp
    (contDiff_apply ℝ ℝ (1 : Fin 2))
  have hU1 := (axisBoxUpperTransition_smooth d δ).comp
    (contDiff_apply ℝ ℝ (1 : Fin 2))
  simpa only [Function.comp_apply] using ((hL0.mul hU0).mul hL1).mul hU1

theorem axisBoxLowerTransition_nonneg (a δ t : ℝ) :
    0 ≤ axisBoxLowerTransition a δ t :=
  smoothTransitionProfile.nonneg _

theorem axisBoxUpperTransition_nonneg (b δ t : ℝ) :
    0 ≤ axisBoxUpperTransition b δ t :=
  smoothTransitionProfile.nonneg _

theorem axisBoxLowerTransition_le_one (a δ t : ℝ) :
    axisBoxLowerTransition a δ t ≤ 1 :=
  smoothTransitionProfile.le_one _

theorem axisBoxUpperTransition_le_one (b δ t : ℝ) :
    axisBoxUpperTransition b δ t ≤ 1 :=
  smoothTransitionProfile.le_one _

theorem axisBoxLowerTransition_eq_one_of_add_delta_le
    {a δ t : ℝ} (hδ : 0 < δ) (ht : a + δ ≤ t) :
    axisBoxLowerTransition a δ t = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  rw [le_sub_iff_add_le]
  rw [le_div_iff₀ (by linarith : 0 < δ / 2)]
  linarith

theorem axisBoxUpperTransition_eq_one_of_add_delta_le
    {b δ t : ℝ} (hδ : 0 < δ) (ht : t + δ ≤ b) :
    axisBoxUpperTransition b δ t = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  rw [le_sub_iff_add_le]
  rw [le_div_iff₀ (by linarith : 0 < δ / 2)]
  linarith

theorem axisBoxLowerTransition_eq_zero_of_le_add_half_delta
    {a δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ a + δ / 2) :
    axisBoxLowerTransition a δ t = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  rw [sub_nonpos]
  rw [div_le_one₀ (by linarith : 0 < δ / 2)]
  linarith

theorem axisBoxUpperTransition_eq_zero_of_sub_half_delta_le
    {b δ t : ℝ} (hδ : 0 < δ) (ht : b - δ / 2 ≤ t) :
    axisBoxUpperTransition b δ t = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  rw [sub_nonpos]
  rw [div_le_one₀ (by linarith : 0 < δ / 2)]
  linarith

/-- The cutoff takes values in `[0, 1]`. -/
theorem axisBoxInteriorCutoff_nonneg (a b c d δ : ℝ) (x : Vec 2) :
    0 ≤ axisBoxInteriorCutoff a b c d δ x := by
  unfold axisBoxInteriorCutoff
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (axisBoxLowerTransition_nonneg _ _ _)
        (axisBoxUpperTransition_nonneg _ _ _))
      (axisBoxLowerTransition_nonneg _ _ _))
    (axisBoxUpperTransition_nonneg _ _ _)

theorem axisBoxInteriorCutoff_le_one (a b c d δ : ℝ) (x : Vec 2) :
    axisBoxInteriorCutoff a b c d δ x ≤ 1 := by
  unfold axisBoxInteriorCutoff
  have h0 : axisBoxLowerTransition a δ (x 0) *
      axisBoxUpperTransition b δ (x 0) ≤ 1 := by
    exact (mul_le_of_le_one_left (axisBoxUpperTransition_nonneg _ _ _)
      (axisBoxLowerTransition_le_one _ _ _)).trans
      (axisBoxUpperTransition_le_one _ _ _)
  have h1 : axisBoxLowerTransition c δ (x 1) *
      axisBoxUpperTransition d δ (x 1) ≤ 1 := by
    exact (mul_le_of_le_one_left (axisBoxUpperTransition_nonneg _ _ _)
      (axisBoxLowerTransition_le_one _ _ _)).trans
      (axisBoxUpperTransition_le_one _ _ _)
  calc
    axisBoxLowerTransition a δ (x 0) *
        axisBoxUpperTransition b δ (x 0) *
          axisBoxLowerTransition c δ (x 1) *
            axisBoxUpperTransition d δ (x 1) =
        (axisBoxLowerTransition a δ (x 0) *
          axisBoxUpperTransition b δ (x 0)) *
          (axisBoxLowerTransition c δ (x 1) *
            axisBoxUpperTransition d δ (x 1)) := by ring
    _ ≤ 1 := (mul_le_of_le_one_left
      (mul_nonneg (axisBoxLowerTransition_nonneg _ _ _)
        (axisBoxUpperTransition_nonneg _ _ _)) h0).trans h1

/-- The cutoff equals one on the closed `δ`-inset. -/
theorem axisBoxInteriorCutoff_eq_one_on_inset
    {a b c d δ : ℝ} (hδ : 0 < δ) {x : Vec 2}
    (hx : x ∈ axisBoxInteriorInset a b c d δ) :
    axisBoxInteriorCutoff a b c d δ x = 1 := by
  have hx0 := hx (0 : Fin 2) (Set.mem_univ _)
  have hx1 := hx (1 : Fin 2) (Set.mem_univ _)
  change x 0 ∈ Set.Icc (a + δ) (b - δ) at hx0
  change x 1 ∈ Set.Icc (c + δ) (d - δ) at hx1
  have hL0 := axisBoxLowerTransition_eq_one_of_add_delta_le
    (a := a) (δ := δ) (t := x 0) hδ hx0.1
  have hU0 := axisBoxUpperTransition_eq_one_of_add_delta_le
    (b := b) (δ := δ) (t := x 0) hδ (by linarith [hx0.2])
  have hL1 := axisBoxLowerTransition_eq_one_of_add_delta_le
    (a := c) (δ := δ) (t := x 1) hδ hx1.1
  have hU1 := axisBoxUpperTransition_eq_one_of_add_delta_le
    (b := d) (δ := δ) (t := x 1) hδ (by linarith [hx1.2])
  simp only [axisBoxInteriorCutoff, hL0, hU0, hL1, hU1, mul_one]

private def axisBoxInteriorSupportBox (a b c d δ : ℝ) : Set (Vec 2) :=
  Set.pi Set.univ fun i =>
    if i = 0 then Set.Icc (a + δ / 2) (b - δ / 2)
    else Set.Icc (c + δ / 2) (d - δ / 2)

private theorem axisBoxInteriorCutoff_support_subset_supportBox
    {a b c d δ : ℝ} (hδ : 0 < δ) :
    Function.support (axisBoxInteriorCutoff a b c d δ) ⊆
      axisBoxInteriorSupportBox a b c d δ := by
  intro x hx i _
  fin_cases i
  · change a + δ / 2 ≤ x 0 ∧ x 0 ≤ b - δ / 2
    constructor
    · by_contra h
      have hz := axisBoxLowerTransition_eq_zero_of_le_add_half_delta hδ
        (le_of_lt (not_le.mp h))
      apply hx
      simp [axisBoxInteriorCutoff, hz]
    · by_contra h
      have hz := axisBoxUpperTransition_eq_zero_of_sub_half_delta_le hδ
        (le_of_lt (not_le.mp h))
      apply hx
      simp [axisBoxInteriorCutoff, hz]
  · change c + δ / 2 ≤ x 1 ∧ x 1 ≤ d - δ / 2
    constructor
    · by_contra h
      have hz := axisBoxLowerTransition_eq_zero_of_le_add_half_delta hδ
        (le_of_lt (not_le.mp h))
      apply hx
      simp [axisBoxInteriorCutoff, hz]
    · by_contra h
      have hz := axisBoxUpperTransition_eq_zero_of_sub_half_delta_le hδ
        (le_of_lt (not_le.mp h))
      apply hx
      simp [axisBoxInteriorCutoff, hz]

private theorem isCompact_axisBoxInteriorSupportBox
    (a b c d δ : ℝ) :
    IsCompact (axisBoxInteriorSupportBox a b c d δ) := by
  unfold axisBoxInteriorSupportBox
  apply isCompact_univ_pi
  intro i
  fin_cases i <;> exact isCompact_Icc

private theorem axisBoxInteriorSupportBox_subset_axisBox
    {a b c d δ : ℝ} (hδ : 0 < δ) :
    axisBoxInteriorSupportBox a b c d δ ⊆
      axisBox ![a, c] ![b, d] := by
  intro x hx i _
  fin_cases i
  · have h := hx (0 : Fin 2) (Set.mem_univ _)
    change a + δ / 2 ≤ x 0 ∧ x 0 ≤ b - δ / 2 at h
    change a < x 0 ∧ x 0 < b
    constructor <;> linarith
  · have h := hx (1 : Fin 2) (Set.mem_univ _)
    change c + δ / 2 ≤ x 1 ∧ x 1 ≤ d - δ / 2 at h
    change c < x 1 ∧ x 1 < d
    constructor <;> linarith

/-- The topological support lies strictly in the open box. -/
theorem axisBoxInteriorCutoff_tsupport_subset
    {a b c d δ : ℝ} (hδ : 0 < δ) :
    tsupport (axisBoxInteriorCutoff a b c d δ) ⊆
      axisBox ![a, c] ![b, d] := by
  exact (closure_minimal
    (axisBoxInteriorCutoff_support_subset_supportBox hδ)
    (isCompact_axisBoxInteriorSupportBox _ _ _ _ _).isClosed).trans
      (axisBoxInteriorSupportBox_subset_axisBox hδ)

/-- The box cutoff has compact topological support. -/
theorem axisBoxInteriorCutoff_hasCompactSupport
    (a b c d : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (axisBoxInteriorCutoff a b c d δ) := by
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_axisBoxInteriorSupportBox _ _ _ _ _)
    (axisBoxInteriorCutoff_support_subset_supportBox hδ)

private def axisBoxTransitionProduct
    (a b δ : ℝ) (t : ℝ) : ℝ :=
  axisBoxLowerTransition a δ t * axisBoxUpperTransition b δ t

private theorem axisBoxLowerTransition_hasDerivAt
    {a δ t : ℝ} :
    HasDerivAt (axisBoxLowerTransition a δ)
      (deriv smoothTransitionProfile ((t - a) / (δ / 2) - 1) *
        (δ / 2)⁻¹) t := by
  have hargument : HasDerivAt (fun s : ℝ => (s - a) / (δ / 2) - 1)
      ((δ / 2)⁻¹) t := by
    have h := (((hasDerivAt_id' t).sub_const a).div_const (δ / 2)).sub_const 1
    rw [one_div] at h
    exact h
  have hprofile : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile ((t - a) / (δ / 2) - 1))
      ((t - a) / (δ / 2) - 1) :=
    (smoothTransitionProfile.smooth.differentiable (by simp) _).hasDerivAt
  simpa only [axisBoxLowerTransition, Function.comp_apply] using!
    hprofile.comp t hargument

private theorem axisBoxUpperTransition_hasDerivAt
    {b δ t : ℝ} :
    HasDerivAt (axisBoxUpperTransition b δ)
      (deriv smoothTransitionProfile ((b - t) / (δ / 2) - 1) *
        (-(δ / 2)⁻¹)) t := by
  have hargument : HasDerivAt (fun s : ℝ => (b - s) / (δ / 2) - 1)
      (-(δ / 2)⁻¹) t := by
    have h := (((hasDerivAt_id' t).const_sub b).div_const (δ / 2)).sub_const 1
    rw [neg_div, one_div] at h
    exact h
  have hprofile : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile ((b - t) / (δ / 2) - 1))
      ((b - t) / (δ / 2) - 1) :=
    (smoothTransitionProfile.smooth.differentiable (by simp) _).hasDerivAt
  simpa only [axisBoxUpperTransition, Function.comp_apply] using!
    hprofile.comp t hargument

private theorem abs_deriv_axisBoxLowerTransition_le
    {a δ t : ℝ} (hδ : 0 < δ) :
    |deriv (axisBoxLowerTransition a δ) t| ≤ 16 / δ := by
  rw [axisBoxLowerTransition_hasDerivAt.deriv]
  have hhalf : 0 < δ / 2 := by linarith
  have hinv : |(δ / 2)⁻¹| = 2 / δ := by
    rw [abs_inv, abs_of_pos hhalf, inv_div]
  rw [abs_mul, hinv]
  calc
    |deriv smoothTransitionProfile ((t - a) / (δ / 2) - 1)| *
          (2 / δ) ≤
        8 * (2 / δ) :=
      mul_le_mul_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _)
        (by positivity)
    _ = 16 / δ := by ring

private theorem abs_deriv_axisBoxUpperTransition_le
    {b δ t : ℝ} (hδ : 0 < δ) :
    |deriv (axisBoxUpperTransition b δ) t| ≤ 16 / δ := by
  rw [axisBoxUpperTransition_hasDerivAt.deriv]
  have hhalf : 0 < δ / 2 := by linarith
  have hinv : |-(δ / 2)⁻¹| = 2 / δ := by
    rw [abs_neg, abs_inv, abs_of_pos hhalf, inv_div]
  rw [abs_mul, hinv]
  calc
    |deriv smoothTransitionProfile ((b - t) / (δ / 2) - 1)| *
          (2 / δ) ≤
        8 * (2 / δ) :=
      mul_le_mul_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _)
        (by positivity)
    _ = 16 / δ := by ring

private theorem axisBoxTransitionProduct_hasDerivAt
    {a b δ t : ℝ} :
    HasDerivAt (axisBoxTransitionProduct a b δ)
      (deriv (axisBoxLowerTransition a δ) t *
          axisBoxUpperTransition b δ t +
          axisBoxLowerTransition a δ t *
          deriv (axisBoxUpperTransition b δ) t) t := by
  change HasDerivAt
    (axisBoxLowerTransition a δ * axisBoxUpperTransition b δ) _ t
  have hlower := axisBoxLowerTransition_hasDerivAt (a := a) (δ := δ) (t := t)
  have hupper := axisBoxUpperTransition_hasDerivAt (b := b) (δ := δ) (t := t)
  rw [hlower.deriv, hupper.deriv]
  exact hlower.mul hupper

private theorem abs_deriv_axisBoxTransitionProduct_le
    {a b δ t : ℝ} (hδ : 0 < δ) :
    |deriv (axisBoxTransitionProduct a b δ) t| ≤ 32 / δ := by
  rw [axisBoxTransitionProduct_hasDerivAt.deriv]
  calc
    |deriv (axisBoxLowerTransition a δ) t *
          axisBoxUpperTransition b δ t +
        axisBoxLowerTransition a δ t *
          deriv (axisBoxUpperTransition b δ) t| ≤
      |deriv (axisBoxLowerTransition a δ) t *
          axisBoxUpperTransition b δ t| +
        |axisBoxLowerTransition a δ t *
          deriv (axisBoxUpperTransition b δ) t| :=
      abs_add_le _ _
    _ =
      |deriv (axisBoxLowerTransition a δ) t| *
          |axisBoxUpperTransition b δ t| +
        |axisBoxLowerTransition a δ t| *
          |deriv (axisBoxUpperTransition b δ) t| := by
      rw [abs_mul, abs_mul]
    _ ≤ (16 / δ) * 1 + 1 * (16 / δ) := by
      gcongr
      · exact abs_deriv_axisBoxLowerTransition_le hδ
      · rw [abs_of_nonneg (axisBoxUpperTransition_nonneg _ _ _)]
        exact axisBoxUpperTransition_le_one _ _ _
      · rw [abs_of_nonneg (axisBoxLowerTransition_nonneg _ _ _)]
        exact axisBoxLowerTransition_le_one _ _ _
      · exact abs_deriv_axisBoxUpperTransition_le hδ
    _ = 32 / δ := by ring

private theorem fderiv_axisBoxTransitionProduct_comp_apply
    {a b δ : ℝ} (i j : Fin 2) (x : Vec 2) :
    (fderiv ℝ (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y i)) x)
        (basisVec j) =
      deriv (axisBoxTransitionProduct a b δ) (x i) * basisVec j i := by
  have hscalar := axisBoxTransitionProduct_hasDerivAt
    (a := a) (b := b) (δ := δ) (t := x i)
  have hcoordinate : HasFDerivAt (fun y : Vec 2 => y i)
      ((ContinuousLinearMap.proj i) : Vec 2 →L[ℝ] ℝ) x :=
    hasFDerivAt_apply (𝕜 := ℝ) i x
  have hvector : HasFDerivAt
      (axisBoxTransitionProduct a b δ ∘ fun y : Vec 2 => y i)
      (deriv (axisBoxTransitionProduct a b δ) (x i) •
        ((ContinuousLinearMap.proj i) : Vec 2 →L[ℝ] ℝ)) x :=
    by simpa only [← hscalar.deriv] using
      hscalar.comp_hasFDerivAt x hcoordinate
  change
    (fderiv ℝ (axisBoxTransitionProduct a b δ ∘ fun y : Vec 2 => y i) x)
        (basisVec j) = _
  rw [hvector.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]

private theorem classicalGradient_axisBoxTransitionProduct_comp_apply
    {a b δ : ℝ} (i j : Fin 2) (x : Vec 2) :
    classicalGradient (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y i)) x j =
      deriv (axisBoxTransitionProduct a b δ) (x i) * basisVec j i := by
  rw [classicalGradient_apply]
  exact fderiv_axisBoxTransitionProduct_comp_apply i j x

private theorem axisBoxInteriorCutoff_apply_as_transitionProducts
    (a b c d δ : ℝ) (x : Vec 2) :
    axisBoxInteriorCutoff a b c d δ x =
      axisBoxTransitionProduct a b δ (x 0) *
        axisBoxTransitionProduct c d δ (x 1) := by
  simp only [axisBoxInteriorCutoff, axisBoxTransitionProduct]
  ring

private theorem differentiableAt_axisBoxTransitionProduct_comp
    {a b δ : ℝ} (i : Fin 2) (x : Vec 2) :
    DifferentiableAt ℝ
      (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y i)) x := by
  have hcoordinate : HasFDerivAt (fun y : Vec 2 => y i)
      ((ContinuousLinearMap.proj i) : Vec 2 →L[ℝ] ℝ) x :=
    hasFDerivAt_apply (𝕜 := ℝ) i x
  have hvector : HasFDerivAt
      (axisBoxTransitionProduct a b δ ∘ fun y : Vec 2 => y i)
      (deriv (axisBoxTransitionProduct a b δ) (x i) •
        ((ContinuousLinearMap.proj i) : Vec 2 →L[ℝ] ℝ)) x :=
    by
      have hscalar := axisBoxTransitionProduct_hasDerivAt
        (a := a) (b := b) (δ := δ) (t := x i)
      simpa only [← hscalar.deriv] using
        hscalar.comp_hasFDerivAt x hcoordinate
  simpa only [Function.comp_apply] using! hvector.differentiableAt

/-- Each coordinate of the classical gradient is bounded by `32 / δ`. -/
theorem abs_classicalGradient_axisBoxInteriorCutoff_apply_le
    {a b c d δ : ℝ} (hδ : 0 < δ) (x : Vec 2) (i : Fin 2) :
    |classicalGradient (axisBoxInteriorCutoff a b c d δ) x i| ≤ 32 / δ := by
  fin_cases i
  · have hfirst : DifferentiableAt ℝ
        (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y 0)) x :=
      differentiableAt_axisBoxTransitionProduct_comp (a := a) (b := b) 0 x
    have hsecond : DifferentiableAt ℝ
        (fun y : Vec 2 => axisBoxTransitionProduct c d δ (y 1)) x :=
      differentiableAt_axisBoxTransitionProduct_comp (a := c) (b := d) 1 x
    rw [show axisBoxInteriorCutoff a b c d δ =
      (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y 0)) *
        (fun y : Vec 2 => axisBoxTransitionProduct c d δ (y 1)) by
          funext y
          exact axisBoxInteriorCutoff_apply_as_transitionProducts _ _ _ _ _ _,
      classicalGradient_apply, fderiv_mul hfirst hsecond]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    have hright := fderiv_axisBoxTransitionProduct_comp_apply
      (a := c) (b := d) (δ := δ) (i := (1 : Fin 2)) (j := (0 : Fin 2)) x
    have hleft := fderiv_axisBoxTransitionProduct_comp_apply
      (a := a) (b := b) (δ := δ) (i := (0 : Fin 2)) (j := (0 : Fin 2)) x
    change
      |axisBoxTransitionProduct a b δ (x 0) *
            (fderiv ℝ
              (fun y : Vec 2 => axisBoxTransitionProduct c d δ (y 1)) x)
              (basisVec (0 : Fin 2)) +
          axisBoxTransitionProduct c d δ (x 1) *
            (fderiv ℝ
              (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y 0)) x)
              (basisVec (0 : Fin 2))| ≤ 32 / δ
    rw [hright, hleft]
    rw [basisVec_apply, basisVec_apply, ite_eq_left rfl, ite_eq_right (by decide)]
    simp only [mul_one, mul_zero, zero_add, abs_mul]
    calc
      |axisBoxTransitionProduct c d δ (x 1)| *
          |deriv (axisBoxTransitionProduct a b δ) (x 0)| ≤
        1 * (32 / δ) := by
        gcongr
        · rw [axisBoxTransitionProduct,
            abs_of_nonneg (mul_nonneg
              (axisBoxLowerTransition_nonneg _ _ _)
              (axisBoxUpperTransition_nonneg _ _ _))]
          exact (mul_le_of_le_one_left (axisBoxUpperTransition_nonneg _ _ _)
            (axisBoxLowerTransition_le_one _ _ _)).trans
            (axisBoxUpperTransition_le_one _ _ _)
        · exact abs_deriv_axisBoxTransitionProduct_le hδ
      _ = 32 / δ := by ring
  · have hfirst : DifferentiableAt ℝ
        (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y 0)) x :=
      differentiableAt_axisBoxTransitionProduct_comp (a := a) (b := b) 0 x
    have hsecond : DifferentiableAt ℝ
        (fun y : Vec 2 => axisBoxTransitionProduct c d δ (y 1)) x :=
      differentiableAt_axisBoxTransitionProduct_comp (a := c) (b := d) 1 x
    rw [show axisBoxInteriorCutoff a b c d δ =
      (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y 0)) *
        (fun y : Vec 2 => axisBoxTransitionProduct c d δ (y 1)) by
          funext y
          exact axisBoxInteriorCutoff_apply_as_transitionProducts _ _ _ _ _ _,
      classicalGradient_apply, fderiv_mul hfirst hsecond]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    have hright := fderiv_axisBoxTransitionProduct_comp_apply
      (a := c) (b := d) (δ := δ) (i := (1 : Fin 2)) (j := (1 : Fin 2)) x
    have hleft := fderiv_axisBoxTransitionProduct_comp_apply
      (a := a) (b := b) (δ := δ) (i := (0 : Fin 2)) (j := (1 : Fin 2)) x
    change
      |axisBoxTransitionProduct a b δ (x 0) *
            (fderiv ℝ
              (fun y : Vec 2 => axisBoxTransitionProduct c d δ (y 1)) x)
              (basisVec (1 : Fin 2)) +
          axisBoxTransitionProduct c d δ (x 1) *
            (fderiv ℝ
              (fun y : Vec 2 => axisBoxTransitionProduct a b δ (y 0)) x)
              (basisVec (1 : Fin 2))| ≤ 32 / δ
    rw [hright, hleft]
    rw [basisVec_apply, basisVec_apply, ite_eq_left rfl, ite_eq_right (by decide)]
    simp only [mul_zero, mul_one, add_zero, abs_mul]
    calc
      |axisBoxTransitionProduct a b δ (x 0)| *
          |deriv (axisBoxTransitionProduct c d δ) (x 1)| ≤
        1 * (32 / δ) := by
        gcongr
        · rw [axisBoxTransitionProduct,
            abs_of_nonneg (mul_nonneg
              (axisBoxLowerTransition_nonneg _ _ _)
              (axisBoxUpperTransition_nonneg _ _ _))]
          exact (mul_le_of_le_one_left (axisBoxUpperTransition_nonneg _ _ _)
            (axisBoxLowerTransition_le_one _ _ _)).trans
            (axisBoxUpperTransition_le_one _ _ _)
        · exact abs_deriv_axisBoxTransitionProduct_le hδ
      _ = 32 / δ := by ring

/-- The explicit Euclidean gradient bound for the planar axis-box cutoff. -/
theorem axisBoxInteriorCutoff_gradient_bound
    {a b c d δ : ℝ} (hδ : 0 < δ) (x : Vec 2) :
    vecEuclideanNorm (classicalGradient (axisBoxInteriorCutoff a b c d δ) x) ≤
      64 / δ := by
  calc
    vecEuclideanNorm (classicalGradient (axisBoxInteriorCutoff a b c d δ) x) ≤
      ∑ i : Fin 2, |classicalGradient (axisBoxInteriorCutoff a b c d δ) x i| :=
      vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin 2, 32 / δ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact abs_classicalGradient_axisBoxInteriorCutoff_apply_le hδ x i
    _ = 64 / δ := by
      rw [Fin.sum_univ_two]
      ring

/-- The quantitative smooth cutoff on a planar axis box, with gradient
constant `64 / δ`. -/
def axisBoxInteriorQuantitativeSmoothCutoff
    (a b c d : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    QuantitativeSmoothCutoff
      (axisBoxInteriorInset a b c d δ)
      (axisBox ![a, c] ![b, d]) (64 / δ) where
  toFun := axisBoxInteriorCutoff a b c d δ
  smooth := axisBoxInteriorCutoff_smooth _ _ _ _ _
  hasCompactSupport := axisBoxInteriorCutoff_hasCompactSupport _ _ _ _ hδ
  tsupport_subset := axisBoxInteriorCutoff_tsupport_subset hδ
  nonneg := axisBoxInteriorCutoff_nonneg _ _ _ _ _
  le_one := axisBoxInteriorCutoff_le_one _ _ _ _ _
  eq_one_on_inner := fun _ hx =>
    axisBoxInteriorCutoff_eq_one_on_inset hδ hx
  gradient_bound := axisBoxInteriorCutoff_gradient_bound hδ

end PDE
