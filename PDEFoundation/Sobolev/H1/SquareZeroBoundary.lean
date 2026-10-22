module

public import PDEFoundation.Measure.ShrinkingAxisBoxCollar
public import PDEFoundation.Sobolev.Cutoff.AxisBox
public import PDEFoundation.Sobolev.H1.AxisBoxCutoffError
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
public import PDEFoundation.Sobolev.H1.ZeroBoundaryLimit
public import PDEFoundation.Sobolev.Trace.SquareCollarUnion

/-!
# Square traces and the zero-boundary positive part

This module contains the quantitative cutoff-convergence ingredients for the
square trace criterion.  The cutoff width is the explicit sequence
`r / (n + 2)`.  The first lemma records its admissible range; the second one
records the part of the convergence argument which needs only local `L²`
integrability: the positive-part value energy on the shrinking collar tends
to zero.

The main theorem combines these limits with the explicit normal-derivative
collar estimate and the supported-cutoff closure theorem.
-/

@[expose] public section

noncomputable section

namespace PDE

open scoped Topology

open Filter MeasureTheory Set

/-- The canonical width `r / (n + 2)` is positive and is admissible for a
width-`2r` square collar whenever `r > 0`. -/
theorem canonicalAxisBoxCollarWidth_mem_Icc
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    r / ((n : ℝ) + 2) ∈ Icc 0 (2 * r) := by
  have hn : 0 < (n : ℝ) + 2 := by positivity
  constructor
  · exact div_nonneg hr.le hn.le
  · rw [div_le_iff₀ hn]
    have hn' : 2 ≤ (n : ℝ) + 2 := by
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith

/-- For the canonical cutoff widths, the squared positive-part value energy
on the complement of the closed inset tends to zero.  This is the exact
shrinking-collar contribution to the value part of the `H¹` convergence
argument; no boundary assumption is used here. -/
theorem H1Function.tendsto_setIntegral_sq_positivePartSubConst_canonical_collar
    {x₀ : Vec 2} {r k : ℝ}
    (u : H1Function (centeredAxisCube x₀ r)) :
    Tendsto (fun n : ℕ =>
      ∫ x in centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2)),
        (max (u.toFun x - k) 0) ^ 2) atTop (𝓝 0) := by
  let Q : Set (Vec 2) := centeredAxisCube x₀ r
  let hQ : IsOpenBoundedConvexDomain Q :=
    isOpenBoundedConvexDomain_centeredAxisCube x₀ r
  let v : H1Function Q := u.positivePartSubConst hQ k
  have hv : IntegrableOn (fun x => (v.toFun x) ^ 2) Q volume := by
    simpa only [IntegrableOn] using v.memL2.integrable_sq
  have hlimit :=
    tendsto_setIntegral_sq_canonical_centeredAxisCubeBoundaryCollar x₀ r hv
  have hset : ∀ n : ℕ,
      centeredAxisCube x₀ r \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2)) =
      centeredAxisCubeBoundaryCollar x₀ r (r / ((n : ℝ) + 2)) := by
    intro n
    exact centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar
      x₀ r _
  simpa only [v, Q, H1Function.positivePartSubConst_toFun, hset] using hlimit

/-- The planar endpoint box is definitionally the centered axis cube.  This
small bridge keeps the cutoff construction on the native `Vec 2` API. -/
theorem planar_axisBox_eq_centeredAxisCube (x₀ : Vec 2) (r : ℝ) :
    axisBox ![x₀ 0 - r, x₀ 1 - r] ![x₀ 0 + r, x₀ 1 + r] =
      centeredAxisCube x₀ r := by
  unfold centeredAxisCube
  congr 1 <;> funext i <;> fin_cases i <;> rfl

namespace H1Function

/-- The concrete `H¹₀` approximation to `(u-k)₊` obtained by multiplying by
the width-`r/(n+2)` planar box cutoff.  The cutoff is unsquared: each native
gradient coordinate has the explicit bound `32 / (r/(n+2))`. -/
noncomputable def canonicalSquarePositivePartCutoffToH10
    {x₀ : Vec 2} {r k : ℝ} (hr : 0 < r)
    (u : H1Function (centeredAxisCube x₀ r)) (n : ℕ) :
    H10Function (centeredAxisCube x₀ r) := by
  let δ : ℝ := r / ((n : ℝ) + 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    apply div_pos hr
    positivity
  let η := axisBoxInteriorQuantitativeSmoothCutoff
    (x₀ 0 - r) (x₀ 0 + r) (x₀ 1 - r) (x₀ 1 + r)
    hδ
  exact (u.positivePartSubConst
    (isOpenBoundedConvexDomain_centeredAxisCube x₀ r) k).mulCutoffToH10
      (isOpenBoundedConvexDomain_centeredAxisCube x₀ r) η
      (by
        simpa only [planar_axisBox_eq_centeredAxisCube] using
          (Set.Subset.rfl : centeredAxisCube x₀ r ⊆ centeredAxisCube x₀ r))

/-- The value representative of the canonical square cutoff approximation is
the literal unsquared cutoff times `(u-k)₊`. -/
theorem canonicalSquarePositivePartCutoffToH10_toFun
    {x₀ : Vec 2} {r k : ℝ} (hr : 0 < r)
    (u : H1Function (centeredAxisCube x₀ r)) (n : ℕ) :
    (u.canonicalSquarePositivePartCutoffToH10 (k := k) hr n).toH1Function.toFun =
      fun x =>
        axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2)) x *
          max (u.toFun x - k) 0 := by
  unfold canonicalSquarePositivePartCutoffToH10
  rw [mulCutoffToH10_toFun, positivePartSubConst_toFun]
  rfl

/-- The gradient representative of the canonical square cutoff approximation.
The second term is the only one requiring the boundary collar estimate in the
subsequent convergence proof. -/
theorem canonicalSquarePositivePartCutoffToH10_grad
    {x₀ : Vec 2} {r k : ℝ} (hr : 0 < r)
    (u : H1Function (centeredAxisCube x₀ r)) (n : ℕ) :
    (u.canonicalSquarePositivePartCutoffToH10 (k := k) hr n).toH1Function.grad =
      fun x =>
        axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2)) x •
            {y | k < u.toFun y}.indicator u.grad x +
          max (u.toFun x - k) 0 •
            classicalGradient
              (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
                (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2))) x := by
  unfold canonicalSquarePositivePartCutoffToH10
  rw [mulCutoffToH10_grad, positivePartSubConst_toFun,
    positivePartSubConst_grad]
  rfl

/-- The coordinatewise cutoff-gradient constant used by the square
zero-boundary approximation.  Keeping this as `32 / δ`, rather than replacing
it by the vector bound, is what lets the four normal-direction collar terms
retain their exact quantitative normalization. -/
theorem abs_classicalGradient_canonicalSquareCutoff_apply_le
    {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) (n : ℕ)
    (x : Vec 2) (i : Fin 2) :
    |classicalGradient
      (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
        (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2))) x i| ≤
      32 / (r / ((n : ℝ) + 2)) := by
  apply abs_classicalGradient_axisBoxInteriorCutoff_apply_le
  apply div_pos hr
  positivity

end H1Function

/-- A common square trace certificate whose four side traces lie below `k`
puts the positive part `(u-k)₊` in the representative-level zero-boundary
space.  The proof uses unsquared cutoffs of width `r / (n + 2)`: the value
and plateau-gradient errors vanish on the shrinking collar, while the normal
trace estimate cancels the cutoff factor `δ⁻²` exactly. -/
theorem SquareNormalTraceCertificate.memH10_positivePartSubConst_of_trace_upper_bounds
    {F : ℕ → Vec 2 → ℝ} {x₀ : Vec 2} {r k : ℝ}
    {u : H1Function (centeredAxisCube x₀ r)}
    (C : SquareNormalTraceCertificate F u.toFun u.grad x₀ r)
    (hleft : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      C.traceProvenance.trace.left t ≤ k)
    (hright : ∀ t ∈ Icc (x₀ 1 - r) (x₀ 1 + r),
      C.traceProvenance.trace.right t ≤ k)
    (hbottom : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      C.traceProvenance.trace.bottom s ≤ k)
    (htop : ∀ s ∈ Icc (x₀ 0 - r) (x₀ 0 + r),
      C.traceProvenance.trace.top s ≤ k) :
    MemH10 (centeredAxisCube x₀ r)
      (u.positivePartSubConst
        (isOpenBoundedConvexDomain_centeredAxisCube x₀ r) k).toFun := by
  let Q : Set (Vec 2) := centeredAxisCube x₀ r
  let hQ : IsOpenBoundedConvexDomain Q :=
    isOpenBoundedConvexDomain_centeredAxisCube x₀ r
  let v : H1Function Q := u.positivePartSubConst hQ k
  let δ : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  let V : ℕ → H10Function Q := fun n =>
    u.canonicalSquarePositivePartCutoffToH10 (k := k) C.radius_pos n
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    exact div_pos C.radius_pos (by positivity)
  have hδrange : ∀ n, δ n ∈ Icc 0 (2 * r) := by
    intro n
    simpa only [δ] using canonicalAxisBoxCollarWidth_mem_Icc C.radius_pos n
  have hQmeas : MeasurableSet Q := hQ.measurableSet
  have hvalue_collar : Tendsto (fun n : ℕ =>
      ∫ x in Q \
        axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (δ n),
        (v.toFun x) ^ 2) atTop (𝓝 0) := by
    simpa only [Q, v, δ, H1Function.positivePartSubConst_toFun] using
      u.tendsto_setIntegral_sq_positivePartSubConst_canonical_collar
  have hvalue_error : Tendsto (fun n : ℕ =>
      ∫ x in Q,
        (v.toFun x -
          axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n) x * v.toFun x) ^ 2)
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hvalue_collar (fun n => ?_) (fun n => ?_)
    · exact integral_nonneg fun _ => sq_nonneg _
    · exact QuantitativeSmoothCutoff.setIntegral_sq_sub_mul_axisBoxInteriorCutoff_le
        (hδpos n) hQmeas v.memL2
  have hplateau_error : ∀ i : Fin 2, Tendsto (fun n : ℕ =>
      ∫ x in Q,
        ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2)
        atTop (𝓝 0) := by
    intro i
    have hgrad_collar :=
      tendsto_setIntegral_sq_canonical_centeredAxisCubeBoundaryCollar x₀ r
        (show IntegrableOn (fun x => (v.grad x i) ^ 2) Q volume by
          simpa only [IntegrableOn] using (v.gradMemL2 i).integrable_sq)
    have hgrad_collar' : Tendsto (fun n : ℕ =>
        ∫ x in Q \ axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (δ n), (v.grad x i) ^ 2)
        atTop (𝓝 0) := by
      simpa only [Q, δ,
        centeredAxisCube_diff_axisBoxInteriorInset_eq_centeredAxisCubeBoundaryCollar]
        using hgrad_collar
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hgrad_collar' (fun n => ?_) (fun n => ?_)
    · exact integral_nonneg fun _ => sq_nonneg _
    · exact QuantitativeSmoothCutoff.setIntegral_sq_one_sub_mul_axisBoxInteriorCutoff_le
        (hδpos n) hQmeas (v.gradMemL2 i)
  have hside_left : Tendsto (fun n : ℕ =>
      ∫ x in centeredSquareLeftCollar x₀ r (δ n), (u.grad x 0) ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_setIntegral_sq_of_subset_canonical_centeredAxisCubeBoundaryCollar
      x₀ r
    · simpa only [Q, IntegrableOn] using
        (u.gradMemL2 0).integrable_sq
    · intro n
      exact centeredSquareLeftCollar_subset_centeredAxisCubeBoundaryCollar
        (hδrange n)
  have hside_right : Tendsto (fun n : ℕ =>
      ∫ x in centeredSquareRightCollar x₀ r (δ n), (u.grad x 0) ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_setIntegral_sq_of_subset_canonical_centeredAxisCubeBoundaryCollar
      x₀ r
    · simpa only [Q, IntegrableOn] using
        (u.gradMemL2 0).integrable_sq
    · intro n
      exact centeredSquareRightCollar_subset_centeredAxisCubeBoundaryCollar
        (hδrange n)
  have hside_bottom : Tendsto (fun n : ℕ =>
      ∫ x in centeredSquareBottomCollar x₀ r (δ n), (u.grad x 1) ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_setIntegral_sq_of_subset_canonical_centeredAxisCubeBoundaryCollar
      x₀ r
    · simpa only [Q, IntegrableOn] using
        (u.gradMemL2 1).integrable_sq
    · intro n
      exact centeredSquareBottomCollar_subset_centeredAxisCubeBoundaryCollar
        (hδrange n)
  have hside_top : Tendsto (fun n : ℕ =>
      ∫ x in centeredSquareTopCollar x₀ r (δ n), (u.grad x 1) ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_setIntegral_sq_of_subset_canonical_centeredAxisCubeBoundaryCollar
      x₀ r
    · simpa only [Q, IntegrableOn] using
        (u.gradMemL2 1).integrable_sq
    · intro n
      exact centeredSquareTopCollar_subset_centeredAxisCubeBoundaryCollar
        (hδrange n)
  have hsides : Tendsto (fun n : ℕ =>
      (∫ x in centeredSquareLeftCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
        (∫ x in centeredSquareRightCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
        (∫ x in centeredSquareBottomCollar x₀ r (δ n), (u.grad x 1) ^ 2) +
        ∫ x in centeredSquareTopCollar x₀ r (δ n), (u.grad x 1) ^ 2)
        atTop (𝓝 0) := by
    simpa using ((hside_left.add hside_right).add hside_bottom).add hside_top
  have hmultiplier_error : ∀ i : Fin 2, Tendsto (fun n : ℕ =>
      ∫ x in Q,
        (v.toFun x * classicalGradient
          (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2)
        atTop (𝓝 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n : ℕ => (1024 : ℝ) *
        ((∫ x in centeredSquareLeftCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
          (∫ x in centeredSquareRightCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
          (∫ x in centeredSquareBottomCollar x₀ r (δ n), (u.grad x 1) ^ 2) +
          ∫ x in centeredSquareTopCollar x₀ r (δ n), (u.grad x 1) ^ 2))
        atTop (𝓝 0) by simpa using tendsto_const_nhds.mul hsides)
      (fun n => ?_) (fun n => ?_)
    · exact integral_nonneg fun _ => sq_nonneg _
    · have hcutoff :=
        QuantitativeSmoothCutoff.setIntegral_sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_le
          (a := x₀ 0 - r) (b := x₀ 0 + r)
          (c := x₀ 1 - r) (d := x₀ 1 + r)
          (hδpos n) hQmeas i v.memL2
      have htrace := C.setIntegral_sq_max_sub_const_le_square_collar
        (hδrange n) hleft hright hbottom htop
      have htrace' :
          ∫ x in Q \ axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n), (v.toFun x) ^ 2 ≤
            (δ n) ^ 2 *
              ((∫ x in centeredSquareLeftCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
                (∫ x in centeredSquareRightCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
                (∫ x in centeredSquareBottomCollar x₀ r (δ n), (u.grad x 1) ^ 2) +
                ∫ x in centeredSquareTopCollar x₀ r (δ n), (u.grad x 1) ^ 2) := by
        simpa only [Q, v, H1Function.positivePartSubConst_toFun] using htrace
      calc
        ∫ x in Q,
          (v.toFun x * classicalGradient
            (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2 ≤
            (32 / δ n) ^ 2 *
              ∫ x in Q \ axisBoxInteriorInset (x₀ 0 - r) (x₀ 0 + r)
                (x₀ 1 - r) (x₀ 1 + r) (δ n), (v.toFun x) ^ 2 := hcutoff
        _ ≤ (32 / δ n) ^ 2 *
            ((δ n) ^ 2 *
              ((∫ x in centeredSquareLeftCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
                (∫ x in centeredSquareRightCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
                (∫ x in centeredSquareBottomCollar x₀ r (δ n), (u.grad x 1) ^ 2) +
                ∫ x in centeredSquareTopCollar x₀ r (δ n), (u.grad x 1) ^ 2)) := by
              gcongr
        _ = 1024 *
              ((∫ x in centeredSquareLeftCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
                (∫ x in centeredSquareRightCollar x₀ r (δ n), (u.grad x 0) ^ 2) +
                (∫ x in centeredSquareBottomCollar x₀ r (δ n), (u.grad x 1) ^ 2) +
                ∫ x in centeredSquareTopCollar x₀ r (δ n), (u.grad x 1) ^ 2) := by
              field_simp [ne_of_gt (hδpos n)]
              ring
  refine memH10_of_tendsto_H1 hQ.isOpen v (fun n => (V n).toH1Function)
    (fun n => ⟨V n, rfl⟩) ?_ ?_
  · apply tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun n => v.memL2.sub (V n).toH1Function.memL2)
    simpa only [V, Q, v, δ,
      H1Function.canonicalSquarePositivePartCutoffToH10_toFun] using! hvalue_error
  · intro i
    apply tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun n => (v.gradMemL2 i).sub ((V n).toH1Function.gradMemL2 i))
    have hsum : Tendsto (fun n : ℕ =>
        2 * (∫ x in Q,
          ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2) +
        2 * (∫ x in Q,
          (v.toFun x * classicalGradient
            (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2))
        atTop (𝓝 0) := by
      simpa using ((hplateau_error i).const_mul 2).add
        ((hmultiplier_error i).const_mul 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hsum (fun n => ?_) (fun n => ?_)
    · exact integral_nonneg fun _ => sq_nonneg _
    · have hleft : IntegrableOn
          (fun x => (v.grad x i - (V n).toH1Function.grad x i) ^ 2) Q := by
        simpa only [IntegrableOn] using!
          ((v.gradMemL2 i).sub ((V n).toH1Function.gradMemL2 i)).integrable_sq
      have hAmeas : AEStronglyMeasurable
          (fun x => (1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i)
          (volume.restrict Q) := by
        exact (continuous_const.sub
          (axisBoxInteriorCutoff_smooth (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n)).continuous).aestronglyMeasurable.mul
            (v.gradMemL2 i).aestronglyMeasurable
      have hAint : IntegrableOn
          (fun x => ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2) Q := by
        have hgradSq : IntegrableOn (fun x => (v.grad x i) ^ 2) Q := by
          simpa only [IntegrableOn] using (v.gradMemL2 i).integrable_sq
        apply hgradSq.mono' (hAmeas.pow 2)
        filter_upwards with x
        change ‖((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2‖ ≤
          (v.grad x i) ^ 2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact QuantitativeSmoothCutoff.sq_one_sub_mul_axisBoxInteriorCutoff_le
          (a := x₀ 0 - r) (b := x₀ 0 + r)
          (c := x₀ 1 - r) (d := x₀ 1 + r)
          (hδpos n) (h := fun x => v.grad x i) x
      have hcutoffOne : ContDiff ℝ 1
          (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n)) :=
        (axisBoxInteriorCutoff_smooth (x₀ 0 - r) (x₀ 0 + r)
          (x₀ 1 - r) (x₀ 1 + r) (δ n)).of_le (by simp)
      have hgradCont : Continuous (fun x : Vec 2 =>
          classicalGradient (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) :=
        continuous_apply i |>.comp
          (PDE.ContDiff.continuous_classicalGradient hcutoffOne)
      have hBmeas : AEStronglyMeasurable
          (fun x => v.toFun x * classicalGradient
            (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i)
          (volume.restrict Q) :=
        v.memL2.aestronglyMeasurable.mul hgradCont.aestronglyMeasurable
      have hBint : IntegrableOn
          (fun x => (v.toFun x * classicalGradient
            (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2) Q := by
        have hvalueSq : IntegrableOn (fun x => (v.toFun x) ^ 2) Q := by
          simpa only [IntegrableOn] using v.memL2.integrable_sq
        apply (hvalueSq.const_mul ((32 / δ n) ^ 2)).mono' (hBmeas.pow 2)
        filter_upwards with x
        change ‖(v.toFun x * classicalGradient
          (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2‖ ≤
          (32 / δ n) ^ 2 * (v.toFun x) ^ 2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact QuantitativeSmoothCutoff.sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_le
          (hδpos n) _ i x
      have hA2 : IntegrableOn (fun x =>
          2 * ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2) Q := by
        simpa only [smul_eq_mul] using! hAint.const_mul 2
      have hB2 : IntegrableOn (fun x =>
          2 * (v.toFun x * classicalGradient
            (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2) Q := by
        simpa only [smul_eq_mul] using! hBint.const_mul 2
      have hright : IntegrableOn (fun x =>
          2 * ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
            (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2 +
          2 * (v.toFun x * classicalGradient
            (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2) Q :=
        hA2.add hB2
      calc
        ∫ x in Q, (v.grad x i - (V n).toH1Function.grad x i) ^ 2 ≤
            ∫ x in Q,
              2 * ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
                (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2 +
              2 * (v.toFun x * classicalGradient
                (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
                  (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2 := by
              apply setIntegral_mono_on hleft hright hQmeas
              intro x hx
              have hvgrad : v.grad = fun x =>
                  {y | k < u.toFun y}.indicator u.grad x := by
                dsimp only [v, hQ]
                exact H1Function.positivePartSubConst_grad hQ u k
              have hvvalue : v.toFun = fun x => max (u.toFun x - k) 0 := by
                dsimp only [v, hQ]
                exact H1Function.positivePartSubConst_toFun hQ u k
              rw [H1Function.canonicalSquarePositivePartCutoffToH10_grad]
              rw [hvgrad, hvvalue]
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, δ]
              nlinarith [sq_nonneg
                (((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
                  (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2)) x) *
                    {y | k < u.toFun y}.indicator u.grad x i) +
                  max (u.toFun x - k) 0 * classicalGradient
                    (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
                      (x₀ 1 - r) (x₀ 1 + r) (r / ((n : ℝ) + 2))) x i)]
        _ = 2 * (∫ x in Q,
            ((1 - axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
              (x₀ 1 - r) (x₀ 1 + r) (δ n) x) * v.grad x i) ^ 2) +
            2 * (∫ x in Q,
              (v.toFun x * classicalGradient
                (axisBoxInteriorCutoff (x₀ 0 - r) (x₀ 0 + r)
                  (x₀ 1 - r) (x₀ 1 + r) (δ n)) x i) ^ 2) := by
              rw [MeasureTheory.integral_add hA2 hB2, MeasureTheory.integral_const_mul,
                MeasureTheory.integral_const_mul]

end PDE
