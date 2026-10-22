module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceDensity

/-!
# Mollification commutes with weak derivatives locally

If `u` has the weak derivative `g` on an open set `O` and `closedBall x a ⊆ O`, then for a smooth
kernel `K` supported in the closed ball of radius `a` around `0`, the classical derivative of
`K ⋆ u` at `x` equals `(K ⋆ g) x`.  This is the local version of
`euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn` (which requires `O = univ`).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped Convolution

variable {d : ℕ}

private theorem lsmul_flip_eq' :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext; simp

/-- Outside `tsupport φ` both `φ` and its derivative vanish. -/
theorem fderiv_eq_zero_of_notMem_tsupport {φ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport φ) (i : Fin d) : fderiv ℝ φ x (basisVec i) = 0 := by
  have hφEq : φ =ᶠ[nhds x] 0 :=
    (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  rw [Filter.EventuallyEq.fderiv_eq hφEq]
  simp

/-- Local version of the commutation of mollification with weak derivatives. -/
theorem euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn_local
    {K u g : Vec d → ℝ} (hK_supp : HasCompactSupport K)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hu : LocallyIntegrable u volume) {i : Fin d}
    {O : Set (Vec d)} {x : Vec d} {a : ℝ} (hKa : ∀ y : Vec d, a < ‖y‖ → K y = 0)
    (hball : Metric.closedBall x a ⊆ O) (hweak : HasWeakPartialDerivOn O i u g) :
    euclideanCoordDeriv i (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  rw [euclideanCoordDeriv_convolution_left hK_supp hK hu i]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => K (x - y)) :=
    hK.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y : Vec d => K (x - y)) :=
    hK_supp.comp_homeomorph (Homeomorph.subLeft x)
  have hts : tsupport (fun y : Vec d => K (x - y)) ⊆ O := by
    refine (closure_minimal ?_ Metric.isClosed_closedBall).trans hball
    intro y hy
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    by_contra hlt
    exact hy (hKa _ (not_le.mp hlt))
  have hw := hweak _ hφ hφc hts
  have hz1 : ∀ y, y ∉ O → u y * (fderiv ℝ (fun y : Vec d => K (x - y)) y) (basisVec i) = 0 :=
    fun y hy => by
      rw [fderiv_eq_zero_of_notMem_tsupport (fun h => hy (hts h)) i, mul_zero]
  have hz2 : ∀ y, y ∉ O → g y * K (x - y) = 0 := fun y hy => by
    rw [image_eq_zero_of_notMem_tsupport (f := fun y : Vec d => K (x - y))
      (fun h => hy (hts h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz2] at hw
  have hderiv : ∀ y, (fderiv ℝ (fun y : Vec d => K (x - y)) y) (basisVec i) =
      -euclideanCoordDeriv i K (x - y) := fun y =>
    euclideanCoordDeriv_comp_const_sub hK x i y
  simp only [hderiv, mul_neg, integral_neg, neg_inj] at hw
  have hc : ∀ f h : Vec d → ℝ,
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h =
        h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := fun f h => by
    have := convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure (Vec d))) (f := f) (g := h)
    rw [lsmul_flip_eq'] at this
    exact this.symm
  rw [hc (euclideanCoordDeriv i K) u, hc K g]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact hw

end PDE.TraceLane
