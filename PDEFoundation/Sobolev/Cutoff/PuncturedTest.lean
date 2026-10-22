module

public import PDEFoundation.Sobolev.Cutoff.PointRemoval
public import PDEFoundation.Sobolev.WeakDerivative

/-! # Test functions avoiding one point -/

@[expose] public section

namespace PDE

open Filter Set
open scoped Topology

noncomputable section

/-- Multiply a test function by the complement of the canonical point-removal
cutoff.  The result is a test function on the punctured domain. -/
def WeakTestFunction.punctured {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (ε : ℝ) (hε : 0 < ε) :
    WeakTestFunction (U \ {(0 : Vec d)}) where
  toFun := fun x => φ x * (1 - pointRemovalCutoff ε x)
  contDiff := φ.contDiff.mul
    (contDiff_const.sub
      (canonicalBallCutoff_smooth (0 : Vec d) hε.le (by linarith)))
  hasCompactSupport := φ.hasCompactSupport.mul_right
  tsupport_subset := by
    intro x hx
    have hxφ : x ∈ tsupport φ.toFun :=
      tsupport_mul_subset_left hx
    refine ⟨φ.tsupport_subset hxφ, ?_⟩
    intro hx0
    have hxzero : x = 0 := by simpa using hx0
    subst x
    have hball : euclideanBall (0 : Vec d) ε ∈ 𝓝 (0 : Vec d) := by
      exact (isOpen_euclideanBall (0 : Vec d) ε).mem_nhds
        (by
          rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hε]
          rw [show vecEuclideanNorm ((0 : Vec d) - 0) = 0 by
            exact vecEuclideanNorm_eq_zero_iff.mpr (sub_self 0)]
          exact hε)
    have heq :
        (fun y : Vec d => φ y * (1 - pointRemovalCutoff ε y)) =ᶠ[𝓝 0]
          (0 : Vec d → ℝ) := by
      filter_upwards [hball] with y hy
      rw [show pointRemovalCutoff ε y = 1 by
        exact canonicalBallCutoff_eq_one_on_inner hε.le (by linarith) hy]
      simp
    exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hx

@[simp]
theorem WeakTestFunction.punctured_apply {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    φ.punctured ε hε x = φ x * (1 - pointRemovalCutoff ε x) := rfl

/-- Exact product rule for the punctured test function. -/
theorem WeakTestFunction.punctured_partialDeriv {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) {ε : ℝ} (hε : 0 < ε)
    (i : Fin d) (x : Vec d) :
    (φ.punctured ε hε).partialDeriv i x =
      φ.partialDeriv i x * (1 - pointRemovalCutoff ε x) -
        φ x * classicalGradient (pointRemovalCutoff ε) x i := by
  have hφ : DifferentiableAt ℝ φ.toFun x :=
    φ.contDiff.differentiable (by simp) x
  have hηsmooth := canonicalBallCutoff_smooth (0 : Vec d) hε.le
    (by linarith : ε < 2 * ε)
  have hη : DifferentiableAt ℝ (pointRemovalCutoff ε) x :=
    hηsmooth.differentiable (by simp) x
  have hsecond : DifferentiableAt ℝ
      (fun y : Vec d => 1 - pointRemovalCutoff ε y) x :=
    (differentiableAt_const (x := x) (1 : ℝ)).sub hη
  have hfsecond :
      fderiv ℝ (fun y : Vec d => 1 - pointRemovalCutoff ε y) x =
        -fderiv ℝ (pointRemovalCutoff ε) x := by
    exact fderiv_const_sub 1
  unfold WeakTestFunction.partialDeriv
  rw [show (φ.punctured ε hε).toFun =
      φ.toFun * (fun y => 1 - pointRemovalCutoff ε y) by rfl,
    fderiv_mul hφ hsecond, hfsecond]
  simp only [add_apply, smul_apply,
    neg_apply, smul_eq_mul, classicalGradient_apply]
  ring

end

end PDE
