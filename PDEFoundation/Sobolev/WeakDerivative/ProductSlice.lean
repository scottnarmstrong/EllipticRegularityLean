module

public import PDEFoundation.Ambient.VecAppend
public import PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Coordinate slices of weak test functions

A smooth compactly supported test function on a product-coordinate domain can
be restricted to either coordinate slice.  Its global support condition makes
every slice a test function on the corresponding factor, including slices
whose fixed coordinate lies outside the other factor.
-/

@[expose] public section

open Set
open scoped Topology

namespace PDE

def vecAppendRightSlice {m n : ℕ} (y : Vec n) : Vec m → Vec (m + n) :=
  fun x => (vecAppendEquiv m n).symm (x, y)

def vecAppendLeftSlice {m n : ℕ} (x : Vec m) : Vec n → Vec (m + n) :=
  fun y => (vecAppendEquiv m n).symm (x, y)

theorem isClosedEmbedding_vecAppendRightSlice {m n : ℕ} (y : Vec n) :
    Topology.IsClosedEmbedding (vecAppendRightSlice (m := m) y) := by
  have hProd : Isometry (fun x : Vec m => (x, y)) := by
    intro x x'
    simp [Prod.edist_eq]
  exact (vecAppendEquiv m n).symm.toHomeomorph.isClosedEmbedding.comp
    hProd.isClosedEmbedding

theorem isClosedEmbedding_vecAppendLeftSlice {m n : ℕ} (x : Vec m) :
    Topology.IsClosedEmbedding (vecAppendLeftSlice (n := n) x) := by
  have hProd : Isometry (fun y : Vec n => (x, y)) := by
    intro y y'
    simp [Prod.edist_eq]
  exact (vecAppendEquiv m n).symm.toHomeomorph.isClosedEmbedding.comp
    hProd.isClosedEmbedding

theorem contDiff_vecAppendRightSlice {m n : ℕ} (y : Vec n) :
    ContDiff ℝ (⊤ : ℕ∞) (vecAppendRightSlice (m := m) y) := by
  exact (vecAppendEquiv m n).symm.contDiff.comp
    (contDiff_id.prodMk contDiff_const)

theorem contDiff_vecAppendLeftSlice {m n : ℕ} (x : Vec m) :
    ContDiff ℝ (⊤ : ℕ∞) (vecAppendLeftSlice (n := n) x) := by
  exact (vecAppendEquiv m n).symm.contDiff.comp
    (contDiff_const.prodMk contDiff_id)

/-- Fix the remaining coordinates of a test function on a split-coordinate
product domain. -/
def WeakTestFunction.sliceRight {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V))) (y : Vec n) :
    WeakTestFunction U where
  toFun := φ.toFun ∘ vecAppendRightSlice y
  contDiff := φ.contDiff.comp (contDiff_vecAppendRightSlice y)
  hasCompactSupport := φ.hasCompactSupport.comp_isClosedEmbedding
    (isClosedEmbedding_vecAppendRightSlice y)
  tsupport_subset := by
    intro x hx
    have hx' : vecAppendRightSlice y x ∈ tsupport φ.toFun :=
      tsupport_comp_subset_preimage φ.toFun
        (contDiff_vecAppendRightSlice y).continuous hx
    simpa only [vecAppendRightSlice, ContinuousLinearEquiv.apply_symm_apply] using
      (φ.tsupport_subset hx').1

/-- Fix the first coordinates of a test function on a split-coordinate product
domain. -/
def WeakTestFunction.sliceLeft {m n : ℕ} {U : Set (Vec m)} {V : Set (Vec n)}
    (φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V))) (x : Vec m) :
    WeakTestFunction V where
  toFun := φ.toFun ∘ vecAppendLeftSlice x
  contDiff := φ.contDiff.comp (contDiff_vecAppendLeftSlice x)
  hasCompactSupport := φ.hasCompactSupport.comp_isClosedEmbedding
    (isClosedEmbedding_vecAppendLeftSlice x)
  tsupport_subset := by
    intro y hy
    have hy' : vecAppendLeftSlice x y ∈ tsupport φ.toFun :=
      tsupport_comp_subset_preimage φ.toFun
        (contDiff_vecAppendLeftSlice x).continuous hy
    simpa only [vecAppendLeftSlice, ContinuousLinearEquiv.apply_symm_apply] using
      (φ.tsupport_subset hy').2

@[simp]
theorem WeakTestFunction.sliceRight_apply {m n : ℕ} {U : Set (Vec m)}
    {V : Set (Vec n)} (φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))
    (y : Vec n) (x : Vec m) :
    φ.sliceRight y x = φ ((vecAppendEquiv m n).symm (x, y)) := rfl

@[simp]
theorem WeakTestFunction.sliceLeft_apply {m n : ℕ} {U : Set (Vec m)}
    {V : Set (Vec n)} (φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))
    (x : Vec m) (y : Vec n) :
    φ.sliceLeft x y = φ ((vecAppendEquiv m n).symm (x, y)) := rfl

theorem vecAppendEquiv_symm_basis_left {m n : ℕ} (i : Fin m) :
    (vecAppendEquiv m n).symm (basisVec i, 0) =
      basisVec (Fin.castAdd n i) := by
  ext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [basisVec, Pi.single_apply]
  · simp [basisVec, Pi.single_apply]
    intro h
    have := congrArg finSumFinEquiv.symm h
    simp at this

theorem vecAppendEquiv_symm_basis_right {m n : ℕ} (j : Fin n) :
    (vecAppendEquiv m n).symm (0, basisVec j) =
      basisVec (Fin.natAdd m j) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp [basisVec, Pi.single_apply]
    intro h
    have := congrArg finSumFinEquiv.symm h
    simp at this
  · simp [basisVec, Pi.single_apply]

/-- The planar-coordinate derivative of a fixed-right-coordinate slice is the
corresponding derivative of the original test function. -/
theorem WeakTestFunction.sliceRight_partialDeriv {m n : ℕ} {U : Set (Vec m)}
    {V : Set (Vec n)} (φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))
    (y : Vec n) (i : Fin m) (x : Vec m) :
    (φ.sliceRight y).partialDeriv i x =
      φ.partialDeriv (Fin.castAdd n i) ((vecAppendEquiv m n).symm (x, y)) := by
  have hφ : DifferentiableAt ℝ φ.toFun ((vecAppendEquiv m n).symm (x, y)) :=
    φ.contDiff.differentiable (by simp) _
  have hSlice : HasFDerivAt (vecAppendRightSlice y)
      ((vecAppendEquiv m n).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ (Vec m) (Vec n))) x := by
    simpa only [vecAppendRightSlice] using!
      ((vecAppendEquiv m n).symm.hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x y))
  unfold WeakTestFunction.partialDeriv
  rw [show (φ.sliceRight y).toFun = φ.toFun ∘ vecAppendRightSlice y by rfl,
    fderiv_comp x hφ hSlice.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, hSlice.fderiv]
  simpa [vecAppendRightSlice] using
    congrArg (fderiv ℝ φ.toFun ((vecAppendEquiv m n).symm (x, y)))
      (vecAppendEquiv_symm_basis_left (m := m) (n := n) i)

/-- The remaining-coordinate derivative of a fixed-left-coordinate slice is
the corresponding derivative of the original test function. -/
theorem WeakTestFunction.sliceLeft_partialDeriv {m n : ℕ} {U : Set (Vec m)}
    {V : Set (Vec n)} (φ : WeakTestFunction (vecAppendEquiv m n ⁻¹' (U ×ˢ V)))
    (x : Vec m) (j : Fin n) (y : Vec n) :
    (φ.sliceLeft x).partialDeriv j y =
      φ.partialDeriv (Fin.natAdd m j) ((vecAppendEquiv m n).symm (x, y)) := by
  have hφ : DifferentiableAt ℝ φ.toFun ((vecAppendEquiv m n).symm (x, y)) :=
    φ.contDiff.differentiable (by simp) _
  have hSlice : HasFDerivAt (vecAppendLeftSlice x)
      ((vecAppendEquiv m n).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (Vec m) (Vec n))) y := by
    simpa only [vecAppendLeftSlice] using!
      ((vecAppendEquiv m n).symm.hasFDerivAt.comp y
        (hasFDerivAt_prodMk_right x y))
  unfold WeakTestFunction.partialDeriv
  rw [show (φ.sliceLeft x).toFun = φ.toFun ∘ vecAppendLeftSlice x by rfl,
    fderiv_comp y hφ hSlice.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, hSlice.fderiv]
  simpa [vecAppendLeftSlice] using
    congrArg (fderiv ℝ φ.toFun ((vecAppendEquiv m n).symm (x, y)))
      (vecAppendEquiv_symm_basis_right (m := m) (n := n) j)

end PDE
