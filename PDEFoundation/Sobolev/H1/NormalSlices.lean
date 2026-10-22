module

public import PDEFoundation.Sobolev.Trace.NormalSlices
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Summable
public import PDEFoundation.Sobolev.W1p.GraphEnergy

/-!
# `H¹` smooth approximation data for normal slices

This module turns a fixed subsequence of the globally smooth convex
approximation of an `H¹` representative into the concrete data consumed by
the planar normal-slice theorem.  The same sequence is retained verbatim, so
later square-trace and normal-slice constructions can compare their endpoint
limits pointwise.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace H1Function

/-- A fixed convex-approximation subsequence with dyadically summable graph
errors supplies the common smooth data required for both vertical and
horizontal normal-slice limits on an axis box contained in the Sobolev
domain. -/
theorem axisBoxSmoothApproximationData_convexApproxSmoothW1p
    {U : Set (Vec 2)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {x0 : Vec 2} {r : ℝ} (hr : 0 < r)
    {a b c d : ℝ}
    (hbox : axisBox ![a, c] ![b, d] ⊆ U)
    (k : ℕ → ℕ)
    (hsum : Summable fun n => (2 : ℝ) ^ n *
      dist
        ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
          u.toW1pFunction x0 hr (k n)).toW1pGraph)
        u.toW1pFunction.toW1pGraph ^ 2) :
    AxisBoxSmoothApproximationData
      (fun n =>
        (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
          u.toW1pFunction x0 hr (k n)).toFun)
      u.toFun u.grad a b c d := by
  let ψ : ℕ → W1pFunction U (2 : ℝ≥0∞) := fun n =>
    W1pFunction.convexApproxSmoothW1p hU (by norm_num)
      u.toW1pFunction x0 hr (k n)
  let F : ℕ → Vec 2 → ℝ := fun n => (ψ n).toFun
  have hgraph : Summable fun n => (2 : ℝ) ^ n *
      dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2 := by
    simpa only [ψ] using hsum
  have hsmooth : ∀ n, ContDiff ℝ 1 (F n) := by
    intro n
    exact
      (W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU (by norm_num)
        u.toW1pFunction x0 hr (k n)).of_le (by norm_num)
  have hvalueError : ∀ n, MemL2On (axisBox ![a, c] ![b, d])
      (fun x => F n x - u.toFun x) := by
    intro n
    simpa only [F] using!
      memLpOn_mono hbox ((ψ n).memLp.sub u.toW1pFunction.memLp)
  have hgradientError : ∀ n, MemL2On (axisBox ![a, c] ![b, d])
      (fun x => vecEuclideanNorm (classicalGradient (F n) x - u.grad x)) := by
    intro n
    have hmem : MemLpOn U (2 : ℝ≥0∞)
        (fun x => vecEuclideanNorm ((ψ n).grad x - u.grad x)) := by
      apply GradMemLpOn.memLp_vecEuclideanNorm
      intro i
      exact (ψ n).gradMemLp i |>.sub (u.gradMemL2 i)
    have hsub := memLpOn_mono hbox hmem
    simpa only [F, ψ, W1pFunction.convexApproxSmoothW1p_toFun,
      W1pFunction.convexApproxSmoothW1p_grad] using hsub
  have hvalueSum : Summable fun n => (2 : ℝ) ^ n *
      ∫ x in axisBox ![a, c] ![b, d], (F n x - u.toFun x) ^ 2 := by
    have h := H1Function.summable_dyadic_integralOn_sq_sub_toW1pFunction
      ψ u hbox hgraph
    simpa only [F] using h
  have hgradientSum : Summable fun n => (2 : ℝ) ^ n *
      ∫ x in axisBox ![a, c] ![b, d],
        vecEuclideanNorm (classicalGradient (F n) x - u.grad x) ^ 2 := by
    have h := H1Function.summable_dyadic_integralOn_sq_grad_sub_toW1pFunction
      ψ u hbox hgraph
    simpa only [F, ψ, W1pFunction.convexApproxSmoothW1p_toFun,
      W1pFunction.convexApproxSmoothW1p_grad] using h
  refine {
    smooth := hsmooth
    valueMemL2 := memLpOn_mono hbox u.memL2
    gradientMemL2 := fun i => memLpOn_mono hbox (u.gradMemL2 i)
    valueErrorMemL2 := hvalueError
    gradientErrorMemL2 := hgradientError
    valueErrorSummable := hvalueSum
    gradientErrorSummable := hgradientSum }

end H1Function

end

end PDE
