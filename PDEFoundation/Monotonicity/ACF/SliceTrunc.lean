module

public import PDEFoundation.Monotonicity.ACF.SliceTruncApprox
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# ACF-S2: approximation data for a truncation of an `H¹` function

For `u ∈ H¹(B_R)` and `δ ∈ ℝ`, the convex-approximation smoothings of `(u - δ)₊` form a
`SliceApproxData` approximation of `((u - δ)₊, 1_{u > δ} ∇u)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

noncomputable section

variable {d : ℕ}

theorem integrable_vecNormSq_of_coord {μ : Measure (Vec d)} {a : Vec d → Vec d}
    (h : ∀ i, MemLp (fun x => a x i) 2 μ) : Integrable (fun x => vecNormSq (a x)) μ := by
  simp only [vecNormSq_eq_sum_sq]
  exact integrable_finsetSum _ fun i _ => MemLp.integrable_sq (h i)

theorem tendsto_integral_sq_of_eLpNorm {μ : Measure (Vec d)} {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (h : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0) := by
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have h2 := h1.pow 2
  simp only [ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
  refine h2.congr fun n => ?_
  exact toReal_eLpNorm_two_sq_eq_integral_sq (hf n)

/-- The convex-approximation smoothings of the truncation `(u - δ)₊` of an `H¹(B_R)` function
form a `SliceApproxData` approximation of `((u - δ)₊, 1_{u > δ} ∇u)`. -/
theorem exists_truncation_approxData {R : ℝ} (hR : 0 < R) (u : H1Function (euclideanBall (0 : Vec d) R))
    (δ : ℝ) :
    ∃ (r0 : ℝ) (w : ℕ → Vec d → ℝ), 0 < r0 ∧ r0 ≤ R ∧
      Metric.closedBall (0 : Vec d) r0 ⊆ euclideanBall (0 : Vec d) R ∧
      (∀ n, w n = convexApproxSmoothRepresentative (euclideanBall (0 : Vec d) R)
        (unitConvexApproxKernel (d := d)) (fun y => max (u.toFun y - δ) 0) 0 r0
        (unitConvexApproxScale n)) ∧
      SliceApproxData R w (fun y => max (u.toFun y - δ) 0)
        ({y | δ < u.toFun y}.indicator u.grad) := by
  have hU := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR
  obtain ⟨r0, hr0, hr0R, hball⟩ := exists_closedBall_subset_euclideanBall (d := d) hR
  set V := u.positivePartSubConst hU δ with hV
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  set W := fun n => W1pFunction.convexApproxSmoothW1p hU hp V.toW1pFunction (0 : Vec d) hr0 n
    with hW
  have hVv : V.toFun = fun y => max (u.toFun y - δ) 0 := rfl
  have hVg : V.grad = {y | δ < u.toFun y}.indicator u.grad := rfl
  have hWg : ∀ n, (W n).grad = classicalGradient (W n).toFun := fun n => rfl
  have hWv : ∀ n, (W n).toFun = convexApproxSmoothRepresentative (euclideanBall (0 : Vec d) R)
        (unitConvexApproxKernel (d := d)) (fun y => max (u.toFun y - δ) 0) 0 r0
        (unitConvexApproxScale n) := fun n => rfl
  have hVmem : MemLp V.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) := V.memL2
  have hVgmem : ∀ i, MemLp (fun x => V.grad x i) 2
      (volume.restrict (euclideanBall (0 : Vec d) R)) := V.gradMemL2
  have hWmem : ∀ n, MemLp (W n).toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    fun n => (W n).memLp
  have hWgmem : ∀ n i, MemLp (fun x => (W n).grad x i) 2
      (volume.restrict (euclideanBall (0 : Vec d) R)) := fun n => (W n).gradMemLp
  have hdiffg : ∀ n, Integrable (fun x => vecNormSq ((W n).grad x - V.grad x))
      (volume.restrict (euclideanBall (0 : Vec d) R)) := fun n =>
    integrable_vecNormSq_of_coord fun i => (hWgmem n i).sub (hVgmem i)
  refine ⟨r0, fun n => (W n).toFun, hr0, hr0R, hball, hWv, ?_⟩
  rw [← hVv, ← hVg]
  refine
    { w_smooth := fun n => ?_
      v_meas := hVmem.aestronglyMeasurable
      g_meas := fun i => (hVgmem i).aestronglyMeasurable
      v_sq := hVmem.integrable_sq
      g_sq := integrable_vecNormSq_of_coord hVgmem
      w_sq := fun n => (hWmem n).integrable_sq
      dw_sq := fun n => integrable_vecNormSq_of_coord (hWgmem n)
      diff_sq := hdiffg
      diff_v_sq := fun n => ((hWmem n).sub hVmem).integrable_sq
      conv_v := ?_
      conv_g := ?_ }
  · exact (W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU hp V.toW1pFunction
      (0 : Vec d) hr0 n).of_le (by simp)
  · refine (tendsto_integral_sq_of_eLpNorm (f := fun n x => (W n).toFun x - V.toFun x)
      (fun n => (hWmem n).sub hVmem) ?_)
    exact W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp (by norm_num)
      V.toW1pFunction hball hr0
  · have hmeas : ∀ n, AEStronglyMeasurable
        (fun x => vecEuclideanNorm ((W n).grad x - V.grad x))
        (volume.restrict (euclideanBall (0 : Vec d) R)) := fun n =>
      aestronglyMeasurable_vecEuclideanNorm fun i =>
        (hWgmem n i).aestronglyMeasurable.sub (hVgmem i).aestronglyMeasurable
    have hmem : ∀ n, MemLp (fun x => vecEuclideanNorm ((W n).grad x - V.grad x)) 2
        (volume.restrict (euclideanBall (0 : Vec d) R)) := fun n =>
      (memLp_two_iff_integrable_sq (hmeas n)).2 (by
        simpa only [vecEuclideanNorm_sq] using hdiffg n)
    have := tendsto_integral_sq_of_eLpNorm hmem
      (W1pFunction.tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub hU hp (by norm_num)
        V.toW1pFunction hball hr0)
    simp only [vecEuclideanNorm_sq] at this
    exact this

end

end PDE
