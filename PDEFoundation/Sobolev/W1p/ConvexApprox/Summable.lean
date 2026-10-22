module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph
public import Mathlib.Analysis.Normed.Group.Completeness

/-!
# Rapidly Cauchy convex approximation

This module extracts a strictly increasing subsequence from the smooth convex
approximation of a Sobolev representative.  Its graph increments decay fast
enough for the weighted square summability arguments used by boundary-trace
constructions.

The generic metric lemma is kept separate from the Sobolev specialization so
that later complete graph carriers can reuse the same selection argument.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- A Cauchy sequence has a strictly increasing subsequence whose consecutive
increments decay geometrically; their dyadically weighted squares are
summable. -/
theorem exists_strictMono_subseq_geometric_dist_and_summable_of_cauchySeq
    {α : Type*} [PseudoMetricSpace α]
    (v : ℕ → α) (hv : CauchySeq v) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ n, dist (v (f (n + 1))) (v (f n)) ≤ (1 / 8 : ℝ) ^ n) ∧
      Summable (fun n =>
        (2 : ℝ) ^ n * dist (v (f (n + 1))) (v (f n)) ^ 2) := by
  obtain ⟨f, hfMono, hf⟩ :=
    Metric.exists_subseq_bounded_of_cauchySeq v hv
      (fun n => (1 / 8 : ℝ) ^ n)
      (fun n => pow_pos (by norm_num) n)
  refine ⟨f, hfMono, ?_, ?_⟩
  · intro n
    exact le_of_lt <|
      hf n (f (n + 1))
        (hfMono.monotone (Nat.le_succ n))
  · refine Summable.of_nonneg_of_le ?_ ?_
      (summable_geometric_of_lt_one (r := (1 / 32 : ℝ))
        (by norm_num) (by norm_num))
    · intro n
      exact mul_nonneg (pow_nonneg (by norm_num) n) (sq_nonneg _)
    · intro n
      have hdist :
          dist (v (f (n + 1))) (v (f n)) ≤ (1 / 8 : ℝ) ^ n :=
        le_of_lt <|
          hf n (f (n + 1))
            (hfMono.monotone (Nat.le_succ n))
      calc
        (2 : ℝ) ^ n * dist (v (f (n + 1))) (v (f n)) ^ 2 ≤
            (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ n) ^ 2 := by
          gcongr
        _ = (1 / 32 : ℝ) ^ n := by
          calc
            (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ n) ^ 2 =
                (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ 2) ^ n := by
              congr 1
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
            _ = (2 * (1 / 8 : ℝ) ^ 2) ^ n := by
              rw [mul_pow]
            _ = (1 / 32 : ℝ) ^ n := by norm_num

/-- A convergent sequence has a strictly increasing subsequence whose distance
to the actual limit decays geometrically; the dyadically weighted squared
errors are summable. -/
theorem exists_strictMono_subseq_geometric_error_and_summable_of_tendsto
    {α : Type*} [PseudoMetricSpace α]
    (v : ℕ → α) {z : α} (hv : Tendsto v atTop (𝓝 z)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ n, dist (v (f n)) z ≤ (1 / 8 : ℝ) ^ n) ∧
      Summable (fun n =>
        (2 : ℝ) ^ n * dist (v (f n)) z ^ 2) := by
  obtain ⟨f, hfMono, hf⟩ :=
    Metric.exists_subseq_bounded_of_cauchySeq v hv.cauchySeq
      (fun n => (1 / 8 : ℝ) ^ n)
      (fun n => pow_pos (by norm_num) n)
  have hdist :
      ∀ n, dist (v (f n)) z ≤ (1 / 8 : ℝ) ^ n := by
    intro n
    have hlimit :
        dist z (v (f n)) ≤ (1 / 8 : ℝ) ^ n := by
      apply le_of_tendsto (hv.dist tendsto_const_nhds)
      exact
        eventually_atTop.2
          ⟨f n, fun m hm => (hf n m hm).le⟩
    simpa only [dist_comm] using hlimit
  refine ⟨f, hfMono, hdist, ?_⟩
  refine Summable.of_nonneg_of_le ?_ ?_
      (summable_geometric_of_lt_one (r := (1 / 32 : ℝ))
        (by norm_num) (by norm_num))
  · intro n
    exact mul_nonneg (pow_nonneg (by norm_num) n) (sq_nonneg _)
  · intro n
    calc
      (2 : ℝ) ^ n * dist (v (f n)) z ^ 2 ≤
          (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ n) ^ 2 := by
        gcongr
        exact hdist n
      _ = (1 / 32 : ℝ) ^ n := by
        calc
          (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ n) ^ 2 =
              (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ 2) ^ n := by
            congr 1
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
          _ = (2 * (1 / 8 : ℝ) ^ 2) ^ n := by
            rw [mul_pow]
          _ = (1 / 32 : ℝ) ^ n := by norm_num

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The graph images of the globally smooth convex approximants converge to
the graph image of the original `H¹` representative.

The `Metric.closedBall` assumption is the inherited supremum-metric reference cube
used by the convex approximation construction. It is not a round Euclidean
ball. -/
theorem tendsto_convexApproxSmoothW1p_toH1Graph
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {x0 : Vec d} {r : ℝ}
    (hclosedBall : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
          u.toW1pFunction x0 hr n).toW1pGraph)
      atTop (𝓝 u.toW1pFunction.toW1pGraph) := by
  let v : W1pFunction U (2 : ℝ≥0∞) := u.toW1pFunction
  let ψ : ℕ → W1pFunction U (2 : ℝ≥0∞) :=
    W1pFunction.convexApproxSmoothW1p hU (by norm_num) v x0 hr
  rw [tendsto_subtype_rng]
  have hValueLp :
      Tendsto (fun n => (ψ n).memLp.toScalarLp)
        atTop (𝓝 v.memLp.toScalarLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (ψ n).toFun) (fun n => (ψ n).memLp)
        v.toFun v.memLp).mpr
        (W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
          hU (by norm_num) (by norm_num) v hclosedBall hr)
  have hGradientEuclidean :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x => vecEuclideanNorm ((ψ n).grad x - v.grad x))
            2 (volumeOn U))
        atTop (𝓝 0) := by
    apply tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
      (by norm_num)
    · intro n i
      exact ((ψ n).grad_memLp i).aestronglyMeasurable.sub
        (v.grad_memLp i).aestronglyMeasurable
    · intro i
      exact
        W1pFunction.tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
          hU (by norm_num) (by norm_num) v hclosedBall hr i
  have hGradientHilbert :
      Tendsto
        (fun n =>
          eLpNorm
            (toHilbertVecField (ψ n).grad - toHilbertVecField v.grad)
            2 (volumeOn U))
        atTop (𝓝 0) := by
    have hEq : ∀ n,
        eLpNorm (toHilbertVecField fun x => (ψ n).grad x - v.grad x) 2
            (volumeOn U) =
          eLpNorm (fun x => vecEuclideanNorm ((ψ n).grad x - v.grad x)) 2
            (volumeOn U) :=
      fun n => eLpNorm_toHilbertVecField_eq _ _ _
        (aemeasurable_pi_iff.2 fun i =>
          (((ψ n).grad_memLp i).aestronglyMeasurable.sub
            (v.grad_memLp i).aestronglyMeasurable).aemeasurable).aestronglyMeasurable
    simpa only [toHilbertVecField_sub, hEq] using
      hGradientEuclidean
  have hGradientLp :
      Tendsto (fun n => (ψ n).gradMemLp.toHilbertVectorLp)
        atTop (𝓝 v.gradMemLp.toHilbertVectorLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => toHilbertVecField (ψ n).grad)
        (fun n =>
          gradMemLpOn_iff_memLp_toHilbertVecField.mp (ψ n).gradMemLp)
        (toHilbertVecField v.grad)
        (gradMemLpOn_iff_memLp_toHilbertVecField.mp v.gradMemLp)).mpr
        hGradientHilbert
  have hPair :
      Tendsto
        (fun n =>
          weakGradientLpPairOfRepresentatives
            (ψ n).memLp (ψ n).gradMemLp)
        atTop
        (𝓝 (weakGradientLpPairOfRepresentatives v.memLp v.gradMemLp)) := by
    simpa only [weakGradientLpPairOfRepresentatives] using
      hValueLp.prodMk_nhds hGradientLp
  simpa only [ψ, v, W1pFunction.toW1pGraph] using! hPair

/-- Select globally smooth convex approximants with dyadically square-summable
increments in the complete `H¹` graph. -/
theorem exists_strictMono_convexApproxSmoothW1p_summable_h1Graph_increment
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {x0 : Vec d} {r : ℝ}
    (hclosedBall : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ n,
        ContDiff ℝ (⊤ : ℕ∞)
          (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x0 hr (f n)).toFun) ∧
      (∀ n,
        dist
          ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x0 hr (f (n + 1))).toW1pGraph)
          ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x0 hr (f n)).toW1pGraph)
          ≤ (1 / 8 : ℝ) ^ n) ∧
      Summable (fun n =>
        (2 : ℝ) ^ n *
          dist
            ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
              u.toW1pFunction x0 hr (f (n + 1))).toW1pGraph)
            ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
              u.toW1pFunction x0 hr (f n)).toW1pGraph) ^ 2) := by
  obtain ⟨f, hfMono, hdist, hsum⟩ :=
    exists_strictMono_subseq_geometric_dist_and_summable_of_cauchySeq
      (fun n =>
        (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
          u.toW1pFunction x0 hr n).toW1pGraph)
      (tendsto_convexApproxSmoothW1p_toH1Graph hU u hclosedBall hr).cauchySeq
  refine ⟨f, hfMono, ?_, hdist, hsum⟩
  intro n
  exact W1pFunction.contDiff_convexApproxSmoothW1p_toFun
    hU (by norm_num) u.toW1pFunction x0 hr (f n)

/-- Select globally smooth convex approximants whose graph distance to the
given `H¹` representative decays geometrically and whose dyadically weighted
squared errors are summable. -/
theorem exists_strictMono_convexApproxSmoothW1p_summable_h1Graph_error
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {x0 : Vec d} {r : ℝ}
    (hclosedBall : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ n,
        ContDiff ℝ (⊤ : ℕ∞)
          (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x0 hr (f n)).toFun) ∧
      (∀ n,
        dist
          ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x0 hr (f n)).toW1pGraph)
          u.toW1pFunction.toW1pGraph
          ≤ (1 / 8 : ℝ) ^ n) ∧
      Summable (fun n =>
        (2 : ℝ) ^ n *
          dist
            ((W1pFunction.convexApproxSmoothW1p hU (by norm_num)
              u.toW1pFunction x0 hr (f n)).toW1pGraph)
            u.toW1pFunction.toW1pGraph ^ 2) := by
  obtain ⟨f, hfMono, hdist, hsum⟩ :=
    exists_strictMono_subseq_geometric_error_and_summable_of_tendsto
      (fun n =>
        (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
          u.toW1pFunction x0 hr n).toW1pGraph)
      (tendsto_convexApproxSmoothW1p_toH1Graph hU u hclosedBall hr)
  refine ⟨f, hfMono, ?_, hdist, hsum⟩
  intro n
  exact W1pFunction.contDiff_convexApproxSmoothW1p_toFun
    hU (by norm_num) u.toW1pFunction x0 hr (f n)

end H1Function

end PDE
