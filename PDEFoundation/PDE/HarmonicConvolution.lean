module

public import PDEFoundation.Sobolev.ClassicalLaplacian
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Native coordinate calculus for harmonic smoothing

Differentiation of convolution, reflection invariance of the coordinate
Laplacian, and the exact zero-extension pairing dictionary. Extracted from
the sibling harmonic smoothing development with the shared native carrier.
-/

@[expose] public section

namespace PDE

open scoped Convolution

noncomputable section

variable {d : ℕ}

theorem euclideanCoordDeriv_convolution_left {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) (i : Fin d) :
    euclideanCoordDeriv i (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) =
      (euclideanCoordDeriv i K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) := by
  funext x
  unfold euclideanCoordDeriv
  have hderiv :
      fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) x =
        ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d),
          MeasureTheory.volume] g) x) :=
    (hK_supp.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := MeasureTheory.volume) (hf := hK.of_le (by norm_num)) hg x).fderiv
  rw [hderiv]
  calc
    ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d),
          MeasureTheory.volume] g) x) (basisVec i)
        = ((g ⋆[((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)).flip,
            MeasureTheory.volume] fderiv ℝ K) x) (basisVec i) := by
          rw [MeasureTheory.convolution_flip]
    _ = ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR (Vec d),
            MeasureTheory.volume] fderiv ℝ K) x) (basisVec i) := rfl
    _ = (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, MeasureTheory.volume]
            (fun y => (fderiv ℝ K y) (basisVec i))) x :=
          MeasureTheory.convolution_precompR_apply
            (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (f := g) (g := fderiv ℝ K)
            (μ := MeasureTheory.volume) hg (hK_supp.fderiv ℝ)
            (hK.continuous_fderiv (by norm_num)) x (basisVec i)
    _ = ((fun y => (fderiv ℝ K y) (basisVec i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            MeasureTheory.volume] g) x := by
          rw [MeasureTheory.convolution_flip]

/-- Coordinate second derivatives commute with left convolution by a smooth compact kernel. -/
theorem euclideanCoordSecondDeriv_convolution_left {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) (i j : Fin d) :
    euclideanCoordSecondDeriv i j
        (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) =
      (euclideanCoordSecondDeriv i j K ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        MeasureTheory.volume] g) := by
  unfold euclideanCoordSecondDeriv
  rw [euclideanCoordDeriv_convolution_left hK_supp hK hg i]
  exact euclideanCoordDeriv_convolution_left
    (hasCompactSupport_euclideanCoordDeriv hK_supp i)
    (contDiff_euclideanCoordDeriv hK i) hg j

/-- **The coordinate Laplacian commutes with left convolution** by a smooth compactly supported
kernel: `Δ (K ⋆ g) = (Δ K) ⋆ g`. -/
theorem euclideanCoordLaplacian_convolution_left {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) :
    euclideanCoordLaplacian (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) =
      (euclideanCoordLaplacian K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) := by
  funext x
  unfold euclideanCoordLaplacian
  simp_rw [euclideanCoordSecondDeriv_convolution_left hK_supp hK hg]
  simp_rw [MeasureTheory.convolution_def]
  symm
  have hterm : ∀ i : Fin d,
      MeasureTheory.Integrable
        (fun t : Vec d =>
          ContinuousLinearMap.lsmul ℝ ℝ (euclideanCoordSecondDeriv i i K t) (g (x - t)))
        MeasureTheory.volume := by
    intro i
    have h :=
      ((hasCompactSupport_euclideanCoordSecondDeriv hK_supp i
            i).convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (hf := (contDiff_euclideanCoordSecondDeriv hK i i).continuous)
        (hg := hg) x).integrable
    simpa using h
  calc
    ∫ t : Vec d, ContinuousLinearMap.lsmul ℝ ℝ
          (∑ i, euclideanCoordSecondDeriv i i K t) (g (x - t)) ∂MeasureTheory.volume
        = ∫ t : Vec d, ∑ i : Fin d,
            ContinuousLinearMap.lsmul ℝ ℝ (euclideanCoordSecondDeriv i i K t) (g (x - t))
              ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          simp
    _ = ∑ i : Fin d, ∫ t : Vec d,
            ContinuousLinearMap.lsmul ℝ ℝ (euclideanCoordSecondDeriv i i K t) (g (x - t))
              ∂MeasureTheory.volume :=
          MeasureTheory.integral_finsetSum Finset.univ fun i _ => hterm i

/-! ### Behaviour under the point reflection `y ↦ A - y` -/

/-- Coordinate derivative after precomposition with the point reflection `y ↦ A - y`. -/
theorem euclideanCoordDeriv_comp_const_sub {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (A : Vec d) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => K (A - y)) x = -euclideanCoordDeriv i K (A - x) := by
  unfold euclideanCoordDeriv
  have hcomp :
      fderiv ℝ (fun y : Vec d => K (A - y)) x =
        (fderiv ℝ K (A - x)).comp (-(1 : Vec d →L[ℝ] Vec d)) := by
    change fderiv ℝ (K ∘ fun y : Vec d => A - y) x =
      (fderiv ℝ K (A - x)).comp (-(1 : Vec d →L[ℝ] Vec d))
    rw [fderiv_comp]
    · have harg : fderiv ℝ (fun y : Vec d => A - y) x = -(1 : Vec d →L[ℝ] Vec d) := by
        simpa using! (fderiv_const_sub (𝕜 := ℝ) (f := fun y : Vec d => y) (x := x) A)
      rw [harg]
    · exact (hK.differentiable (by simp)) (A - x)
    · fun_prop
  rw [hcomp]
  simp

/-- **The coordinate Laplacian is invariant under the point reflection** `y ↦ A - y`. -/
theorem euclideanCoordLaplacian_comp_const_sub {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (A : Vec d) (x : Vec d) :
    euclideanCoordLaplacian (fun y => K (A - y)) x = euclideanCoordLaplacian K (A - x) := by
  unfold euclideanCoordLaplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold euclideanCoordSecondDeriv
  have hfirst :
      euclideanCoordDeriv i (fun y : Vec d => K (A - y)) =
        fun y => -euclideanCoordDeriv i K (A - y) := by
    funext y
    exact euclideanCoordDeriv_comp_const_sub hK A i y
  rw [hfirst]
  have hD : ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i K) :=
    contDiff_euclideanCoordDeriv hK i
  have href := euclideanCoordDeriv_comp_const_sub hD A i x
  calc
    (fderiv ℝ (fun y : Vec d => -euclideanCoordDeriv i K (A - y)) x) (basisVec i)
        = (-(fderiv ℝ (fun y : Vec d => euclideanCoordDeriv i K (A - y)) x)) (basisVec i) := by
          rw [fderiv_fun_neg]
    _ = -(fderiv ℝ (fun y : Vec d => euclideanCoordDeriv i K (A - y)) x) (basisVec i) := by simp
    _ = -euclideanCoordDeriv i (fun y : Vec d => euclideanCoordDeriv i K (A - y)) x := rfl
    _ = -(-euclideanCoordDeriv i (euclideanCoordDeriv i K) (A - x)) := by rw [href]
    _ = (fderiv ℝ (euclideanCoordDeriv i K) (A - x)) (basisVec i) := by
          simp [euclideanCoordDeriv]

/-! ### Behaviour under the affine homothety `y ↦ a • y + b` -/

/-! ### Reflecting a convolution integral onto the domain -/

/-- **Change of variables by the point reflection** `t ↦ A - t`, converting a global indicator
integral into a set integral over `U`.  This is what turns the value of a convolution against the
zero-extension `1_U u` into a test-function pairing on `U`. -/
theorem integral_mul_indicator_const_sub_eq_setIntegral {U : Set (Vec d)} (hU : MeasurableSet U)
    (A : Vec d) (f u : Vec d → ℝ) :
    ∫ t : Vec d, f t * Set.indicator U u (A - t) ∂MeasureTheory.volume =
      ∫ y in U, u y * f (A - y) ∂MeasureTheory.volume := by
  classical
  let e : Homeomorph (Vec d) (Vec d) := (Homeomorph.neg (Vec d)).trans (Homeomorph.addRight A)
  have heq : (fun y : Vec d => e y) = fun y => A - y := by
    funext y
    simp [e, sub_eq_add_neg, add_comm]
  have hmp_e :
      MeasureTheory.MeasurePreserving e
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume := by
    have hneg :
        MeasureTheory.MeasurePreserving (fun y : Vec d => -y)
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
      MeasureTheory.Measure.measurePreserving_neg _
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : Vec d => y + A)
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) A
    simpa [e] using! hadd.comp hneg
  have hcv :
      ∫ y : Vec d, (fun t : Vec d => f t * Set.indicator U u (A - t)) (e y)
          ∂MeasureTheory.volume =
        ∫ t : Vec d, f t * Set.indicator U u (A - t) ∂MeasureTheory.volume :=
    hmp_e.integral_comp e.measurableEmbedding
      (fun t : Vec d => f t * Set.indicator U u (A - t))
  calc
    ∫ t : Vec d, f t * Set.indicator U u (A - t) ∂MeasureTheory.volume
        = ∫ y : Vec d, f (A - y) * Set.indicator U u y ∂MeasureTheory.volume := by
          rw [← hcv]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          simp [heq, sub_sub_cancel]
    _ = ∫ y : Vec d, Set.indicator U (fun y : Vec d => f (A - y) * u y) y
          ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          by_cases hy : y ∈ U
          · simp [hy]
          · simp [hy]
    _ = ∫ y in U, f (A - y) * u y ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_indicator hU]
    _ = ∫ y in U, u y * f (A - y) ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun hU fun y _ => ?_
          ring

end

end PDE
