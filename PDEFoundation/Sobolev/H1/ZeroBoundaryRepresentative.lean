module

public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.H1.GraphRepresentative

/-!
# Representatives of the zero-boundary `H¹` graph

Every point in the complete zero-boundary graph has a representative-level
`H¹₀` realization, recovered from smooth approximation in the graph norm.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

namespace H10Graph

/-- Every complete zero-boundary graph point is represented by an
`H10Function` whose graph image is the original point. -/
theorem exists_toH10Function (hU : IsOpen U) (z : H10Graph hU) :
    ∃ v : H10Function U, v.toH10Graph hU = z := by
  rcases H10Graph.exists_tendsto_smooth hU z with ⟨φ, hφ⟩
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let u : H1Function U := H1Graph.toH1Function (z : H1Graph U)
  let w : W1pFunction U (2 : ℝ≥0∞) := u.toW1pFunction
  let wSeq : ℕ → W1pFunction U (2 : ℝ≥0∞) := fun n =>
    W1pFunction.ofContDiff hU
      ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2
  have hseq_eq (n : ℕ) :
      (wSeq n).toW1pGraph =
        smoothCompactlySupportedH1Graph hU (φ n) := rfl
  have hlim : w.toW1pGraph = (z : H1Graph U) := by
    dsimp only [w, u]
    exact H1Graph.toW1pGraph_toH1Function (z : H1Graph U)
  have hseq :
      Tendsto (fun n => (wSeq n).toW1pGraph) atTop (𝓝 w.toW1pGraph) := by
    have hsmooth :
        Tendsto (fun n => smoothCompactlySupportedH1Graph hU (φ n))
          atTop (𝓝 (z : H1Graph U)) := hφ
    have hsmooth' :
        Tendsto (fun n => (wSeq n).toW1pGraph)
          atTop (𝓝 (z : H1Graph U)) := by
      simpa only [hseq_eq] using hsmooth
    simpa only [← hlim] using hsmooth'
  have hpair :
      Tendsto (fun n => (wSeq n).toW1pGraph.1)
        atTop (𝓝 (w.toW1pGraph.1)) := by
    simpa only [tendsto_subtype_rng] using hseq
  have hvalueLp :
      Tendsto (fun n => (wSeq n).memLp.toScalarLp)
        atTop (𝓝 (w.memLp.toScalarLp)) := by
    change Tendsto (fun n => (wSeq n).toW1pGraph.1.1)
      atTop (𝓝 (w.toW1pGraph.1.1))
    exact (continuous_fst.tendsto _).comp hpair
  have hvalue :
      Tendsto
        (fun n => eLpNorm ((φ n).toFun - u.toFun)
          (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [wSeq, W1pFunction.ofContDiff] using!
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (wSeq n).toFun) (fun n => (wSeq n).memLp)
        w.toFun w.memLp).mp hvalueLp
  have hgradPair :
      Tendsto (fun n => (wSeq n).toW1pGraph.1.2)
        atTop (𝓝 (w.toW1pGraph.1.2)) := by
    exact (continuous_snd.tendsto _).comp hpair
  have hgradCoordLp (i : Fin d) :
      Tendsto
        (fun n => hilbertVectorLpCoord U (2 : ℝ≥0∞) i
          ((wSeq n).toW1pGraph.1.2))
        atTop
        (𝓝 (hilbertVectorLpCoord U (2 : ℝ≥0∞) i
          (w.toW1pGraph.1.2))) := by
    exact
      ((hilbertVectorLpCoord U (2 : ℝ≥0∞) i).continuous.tendsto _).comp
        hgradPair
  have hcoord_eq (v : W1pFunction U (2 : ℝ≥0∞)) (i : Fin d) :
      hilbertVectorLpCoord U (2 : ℝ≥0∞) i (v.toW1pGraph.1.2) =
        (v.gradMemLp i).toScalarLp := by
    apply Lp.ext
    filter_upwards
      [coeFn_hilbertVectorLpCoord U (2 : ℝ≥0∞) i v.toW1pGraph.1.2,
        v.coeFn_toW1pGraph_snd,
        (v.gradMemLp i).coeFn_toScalarLp]
      with x hcoord hgraph hgrad
    rw [hcoord, hgrad]
    have hgraphCoord := congrArg (fun y : HilbertVec d => y i) hgraph
    simpa only [toHilbertVecField_apply, Vec.toHilbertVec_apply] using
      hgraphCoord
  have hgradLp (i : Fin d) :
      Tendsto (fun n => ((wSeq n).gradMemLp i).toScalarLp)
        atTop (𝓝 ((w.gradMemLp i).toScalarLp)) := by
    simpa only [hcoord_eq] using hgradCoordLp i
  have hgrad (i : Fin d) :
      Tendsto
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (φ n).toFun x) (basisVec i) - u.grad x i)
          (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [wSeq, W1pFunction.ofContDiff] using!
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => fun x => (wSeq n).grad x i)
        (fun n => (wSeq n).gradMemLp i)
        (fun x => w.grad x i) (w.gradMemLp i)).mp (hgradLp i)
  let happrox : u.SupportedSmoothApproximation := {
    approx := fun n => (φ n).toFun
    approx_smooth := fun n => (φ n).contDiff
    approx_hasCompactSupport := fun n => (φ n).hasCompactSupport
    approx_tsupport_subset := fun n => (φ n).tsupport_subset
    tendsto_value := hvalue
    tendsto_grad := hgrad
  }
  refine ⟨u.toH10Function happrox, ?_⟩
  apply Subtype.ext
  change u.toW1pFunction.toW1pGraph = (z : H1Graph U)
  exact hlim

end H10Graph

end PDE
