module

public import PDEFoundation.Sobolev.Trace.SmoothSides
public import PDEFoundation.Sobolev.Trace.VectorErrorLimit

/-!
# Canonical limits on normal coordinate slices

This module defines vertical and horizontal restrictions of planar scalar
functions and applies the one-dimensional smooth vector-error limit theorem.
The resulting representatives are canonical limits of one common planar
approximation sequence, so their endpoint values retain pointwise provenance.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The restriction of a planar scalar function to the vertical line with
first coordinate `s`. -/
def verticalSlice (f : Vec 2 → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun t => f (squarePoint s t)

/-- The restriction of a planar scalar function to the horizontal line with
second coordinate `t`. -/
def horizontalSlice (f : Vec 2 → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s => f (squarePoint s t)

/-- The canonical uniform-Cauchy limit of one common smooth sequence on the
vertical line with first coordinate `s`. -/
def verticalSliceUniformLimit
    (F : ℕ → Vec 2 → ℝ) (s : ℝ) : ℝ → ℝ :=
  uniformCauchySeqLimit fun n => verticalSlice (F n) s

/-- The canonical uniform-Cauchy limit of one common smooth sequence on the
horizontal line with second coordinate `t`. -/
def horizontalSliceUniformLimit
    (F : ℕ → Vec 2 → ℝ) (t : ℝ) : ℝ → ℝ :=
  uniformCauchySeqLimit fun n => horizontalSlice (F n) t

/-- A smooth planar function restricts to a smooth vertical slice. -/
theorem contDiff_verticalSlice
    {f : Vec 2 → ℝ} {n : ℕ∞} (hf : ContDiff ℝ n f) (s : ℝ) :
    ContDiff ℝ n (verticalSlice f s) := by
  have hpoint (t : ℝ) :
      squareLoopRightSide (squarePoint s 0) 0 t =
        squarePoint s t := by
    funext i
    fin_cases i <;> simp [squareLoopRightSide, squarePoint]
  have hslice :
      verticalSlice f s =
        squareLoopRightRestriction f (squarePoint s 0) 0 := by
    funext t
    simp only [verticalSlice, squareLoopRightRestriction]
    rw [hpoint]
  rw [hslice]
  exact contDiff_squareLoopRightRestriction hf (squarePoint s 0) 0

/-- A smooth planar function restricts to a smooth horizontal slice. -/
theorem contDiff_horizontalSlice
    {f : Vec 2 → ℝ} {n : ℕ∞} (hf : ContDiff ℝ n f) (t : ℝ) :
    ContDiff ℝ n (horizontalSlice f t) := by
  have hpoint (s : ℝ) :
      squareLoopTopSide (squarePoint 0 t) 0 s =
        squarePoint s t := by
    funext i
    fin_cases i <;> simp [squareLoopTopSide, squarePoint]
  have hslice :
      horizontalSlice f t =
        squareLoopTopRestriction f (squarePoint 0 t) 0 := by
    funext s
    simp only [horizontalSlice, squareLoopTopRestriction]
    rw [hpoint]
  rw [hslice]
  exact contDiff_squareLoopTopRestriction hf (squarePoint 0 t) 0

/-- The derivative of a smooth vertical slice is coordinate `1` of the
classical gradient. -/
theorem deriv_verticalSlice
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (s t : ℝ) :
    deriv (verticalSlice f s) t =
      classicalGradient f (squarePoint s t) 1 := by
  have hpoint (q : ℝ) :
      squareLoopRightSide (squarePoint s 0) 0 q =
        squarePoint s q := by
    funext i
    fin_cases i <;> simp [squareLoopRightSide, squarePoint]
  have hslice :
      verticalSlice f s =
        squareLoopRightRestriction f (squarePoint s 0) 0 := by
    funext q
    simp only [verticalSlice, squareLoopRightRestriction]
    rw [hpoint]
  rw [hslice, deriv_squareLoopRightRestriction hf]
  rw [hpoint]

/-- The derivative of a smooth horizontal slice is coordinate `0` of the
classical gradient. -/
theorem deriv_horizontalSlice
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (s t : ℝ) :
    deriv (horizontalSlice f t) s =
      classicalGradient f (squarePoint s t) 0 := by
  have hpoint (q : ℝ) :
      squareLoopTopSide (squarePoint 0 t) 0 q =
        squarePoint q t := by
    funext i
    fin_cases i <;> simp [squareLoopTopSide, squarePoint]
  have hslice :
      horizontalSlice f t =
        squareLoopTopRestriction f (squarePoint 0 t) 0 := by
    funext q
    simp only [horizontalSlice, squareLoopTopRestriction]
    rw [hpoint]
  rw [hslice, deriv_squareLoopTopRestriction hf]
  rw [hpoint]

/-- Canonical continuous weak-representative data on one vertical slice. -/
structure HasVerticalNormalSliceLimit
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (c d s : ℝ) : Prop where
  tendstoUniformlyOn :
    TendstoUniformlyOn (fun n => verticalSlice (F n) s)
      (verticalSliceUniformLimit F s) atTop (Icc c d)
  continuousOn :
    ContinuousOn (verticalSliceUniformLimit F s) (Icc c d)
  aeEq :
    verticalSliceUniformLimit F s =ᵐ[volume.restrict (Icc c d)]
      verticalSlice u s
  hasWeakDeriv :
    HasWeakDerivOnIoo c d (verticalSliceUniformLimit F s)
      (fun t => g (squarePoint s t) 1)

/-- Canonical continuous weak-representative data on one horizontal slice. -/
structure HasHorizontalNormalSliceLimit
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b t : ℝ) : Prop where
  tendstoUniformlyOn :
    TendstoUniformlyOn (fun n => horizontalSlice (F n) t)
      (horizontalSliceUniformLimit F t) atTop (Icc a b)
  continuousOn :
    ContinuousOn (horizontalSliceUniformLimit F t) (Icc a b)
  aeEq :
    horizontalSliceUniformLimit F t =ᵐ[volume.restrict (Icc a b)]
      horizontalSlice u t
  hasWeakDeriv :
    HasWeakDerivOnIoo a b (horizontalSliceUniformLimit F t)
      (fun s => g (squarePoint s t) 0)

/-- Pointwise vertical-slice assembly from the exact hypotheses of the
one-dimensional vector-error limit theorem. -/
theorem hasVerticalNormalSliceLimit_of_tendsto_sq_vector_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {c d s : ℝ}
    (hcd : c < d)
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp (verticalSlice u s) 2
      (volume.restrict (Icc c d)))
    (hg : MemLp (fun t => g (squarePoint s t) 1) 2
      (volume.restrict (Icc c d)))
    (hValueError : ∀ n, MemLp
      (fun t => verticalSlice (F n) s t - verticalSlice u s t)
      2 (volume.restrict (Icc c d)))
    (hVectorError : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squarePoint s t) -
          g (squarePoint s t)))
      2 (volume.restrict (Icc c d)))
    (hValue : Tendsto
      (fun n => ∫ t in Icc c d,
        |verticalSlice (F n) s t - verticalSlice u s t| ^ 2)
      atTop (𝓝 0))
    (hVector : Tendsto
      (fun n => ∫ t in Icc c d,
        vecEuclideanNorm
          (classicalGradient (F n) (squarePoint s t) -
            g (squarePoint s t)) ^ 2)
      atTop (𝓝 0)) :
    HasVerticalNormalSliceLimit F u g c d s := by
  let E : ℕ → ℝ → Vec 2 := fun n t =>
    classicalGradient (F n) (squarePoint s t) -
      g (squarePoint s t)
  have hDerivativeError : ∀ n t,
      deriv (verticalSlice (F n) s) t -
        g (squarePoint s t) 1 = E n t 1 := by
    intro n t
    rw [deriv_verticalSlice (hF n) s t]
    rfl
  have hVectorError' : ∀ n,
      MemLp (fun t => vecEuclideanNorm (E n t)) 2
        (volume.restrict (Icc c d)) := by
    intro n
    simpa only [E] using hVectorError n
  have hVector' :
      Tendsto
        (fun n => ∫ t in Icc c d,
          vecEuclideanNorm (E n t) ^ 2)
        atTop (𝓝 0) := by
    simpa only [E] using hVector
  obtain ⟨hUniform, hContinuous, hAe, hWeak⟩ :=
    uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
      (d := 2) (i := 1) (a := c) (b := d)
      (F := fun n => verticalSlice (F n) s)
      (u := verticalSlice u s)
      (g := fun t => g (squarePoint s t) 1)
      (E := E) hcd
      (fun n => contDiff_verticalSlice (hF n) s)
      hu hg hValueError hVectorError' hValue hVector'
      hDerivativeError
  exact ⟨hUniform, hContinuous, hAe, hWeak⟩

/-- Pointwise horizontal-slice assembly from the exact hypotheses of the
one-dimensional vector-error limit theorem. -/
theorem hasHorizontalNormalSliceLimit_of_tendsto_sq_vector_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b t : ℝ}
    (hab : a < b)
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp (horizontalSlice u t) 2
      (volume.restrict (Icc a b)))
    (hg : MemLp (fun s => g (squarePoint s t) 0) 2
      (volume.restrict (Icc a b)))
    (hValueError : ∀ n, MemLp
      (fun s => horizontalSlice (F n) t s -
        horizontalSlice u t s)
      2 (volume.restrict (Icc a b)))
    (hVectorError : ∀ n, MemLp
      (fun s => vecEuclideanNorm
        (classicalGradient (F n) (squarePoint s t) -
          g (squarePoint s t)))
      2 (volume.restrict (Icc a b)))
    (hValue : Tendsto
      (fun n => ∫ s in Icc a b,
        |horizontalSlice (F n) t s - horizontalSlice u t s| ^ 2)
      atTop (𝓝 0))
    (hVector : Tendsto
      (fun n => ∫ s in Icc a b,
        vecEuclideanNorm
          (classicalGradient (F n) (squarePoint s t) -
            g (squarePoint s t)) ^ 2)
      atTop (𝓝 0)) :
    HasHorizontalNormalSliceLimit F u g a b t := by
  let E : ℕ → ℝ → Vec 2 := fun n s =>
    classicalGradient (F n) (squarePoint s t) -
      g (squarePoint s t)
  have hDerivativeError : ∀ n s,
      deriv (horizontalSlice (F n) t) s -
        g (squarePoint s t) 0 = E n s 0 := by
    intro n s
    rw [deriv_horizontalSlice (hF n) s t]
    rfl
  have hVectorError' : ∀ n,
      MemLp (fun s => vecEuclideanNorm (E n s)) 2
        (volume.restrict (Icc a b)) := by
    intro n
    simpa only [E] using hVectorError n
  have hVector' :
      Tendsto
        (fun n => ∫ s in Icc a b,
          vecEuclideanNorm (E n s) ^ 2)
        atTop (𝓝 0) := by
    simpa only [E] using hVector
  obtain ⟨hUniform, hContinuous, hAe, hWeak⟩ :=
    uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
      (d := 2) (i := 0) (a := a) (b := b)
      (F := fun n => horizontalSlice (F n) t)
      (u := horizontalSlice u t)
      (g := fun s => g (squarePoint s t) 0)
      (E := E) hab
      (fun n => contDiff_horizontalSlice (hF n) t)
      hu hg hValueError hVectorError' hValue hVector'
      hDerivativeError
  exact ⟨hUniform, hContinuous, hAe, hWeak⟩

end

end PDE
