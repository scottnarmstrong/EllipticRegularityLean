module

public import PDEFoundation.PDE.HarmonicWeylConvolution
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Consistency of harmonic mollifications at interior points -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Convolution

noncomputable section

variable {d : ℕ}

private theorem euclideanBall_subset_ball_of_margin
    {x₀ x y : Vec d} {r δ R : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hR : 0 < R)
    (hmargin : δ + R < r - vecEuclideanNorm (x - x₀))
    (hy : y ∈ euclideanBall x R) :
    euclideanBall y δ ⊆ euclideanBall x₀ r := by
  have hyx := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hy
  apply euclideanBall_subset_of_center_norm_add_le hδ hr
  have hdecomp : y - x₀ = (y - x) + (x - x₀) := by abel
  have hnorm : vecEuclideanNorm (y - x₀) ≤
      vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := by
    rw [hdecomp]
    exact vecEuclideanNorm_add_le _ _
  linarith

/-- A fixed-scale mollification is harmonic on every ball whose radius plus
its smoothing scale fits strictly inside the original round ball. -/
theorem euclideanCoordLaplacian_harmonicMollify_on_innerBall
    {x₀ x : Vec d} {r δ R : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hR : 0 < R)
    (u : H1Function (euclideanBall x₀ r))
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) (euclideanBall x₀ r) u 0 0)
    (hmargin : δ + R < r - vecEuclideanNorm (x - x₀)) :
    ∀ y ∈ euclideanBall x R,
      euclideanCoordLaplacian (harmonicMollify u δ) y = 0 := by
  intro y hy
  exact euclideanCoordLaplacian_harmonicMollify_eq_zero
    (isOpen_euclideanBall x₀ r) u hsol hδ
    (euclideanBall_subset_ball_of_margin hr hδ hR hmargin hy)

/-- At an interior point, any two sufficiently small positive smoothing
scales give the same harmonic mollification. -/
theorem harmonicMollify_eq_of_scales
    (hd : 0 < d) {x₀ x : Vec d} {r δ ε : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hε : 0 < ε)
    (u : H1Function (euclideanBall x₀ r))
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) (euclideanBall x₀ r) u 0 0)
    (hmargin : δ + ε < r - vecEuclideanNorm (x - x₀)) :
    harmonicMollify u δ x = harmonicMollify u ε x := by
  let m : ℝ := r - vecEuclideanNorm (x - x₀)
  let Rδ : ℝ := (ε + (m - δ)) / 2
  let Rε : ℝ := (δ + (m - ε)) / 2
  have hRδ : 0 < Rδ := by dsimp [Rδ, m]; linarith
  have hRε : 0 < Rε := by dsimp [Rε, m]; linarith
  have hεRδ : ε < Rδ := by dsimp [Rδ, m]; linarith
  have hδRε : δ < Rε := by dsimp [Rε, m]; linarith
  have hδmargin : δ + Rδ < m := by dsimp [Rδ, m]; linarith
  have hεmargin : ε + Rε < m := by dsimp [Rε, m]; linarith
  have hU : IsOpen (euclideanBall x₀ r) := isOpen_euclideanBall x₀ r
  have hδsmooth := contDiff_harmonicMollify hU u hδ
  have hεsmooth := contDiff_harmonicMollify hU u hε
  have hδharm : ∀ y ∈ euclideanBall x Rδ,
      euclideanCoordLaplacian (harmonicMollify u δ) y = 0 :=
    euclideanCoordLaplacian_harmonicMollify_on_innerBall hr hδ hRδ u hsol hδmargin
  have hεharm : ∀ y ∈ euclideanBall x Rε,
      euclideanCoordLaplacian (harmonicMollify u ε) y = 0 :=
    euclideanCoordLaplacian_harmonicMollify_on_innerBall hr hε hRε u hsol hεmargin
  have hrepδ :
      (harmonicKernelScaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        harmonicMollify u δ) x = harmonicMollify u δ x := by
    simpa [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply] using
      (integral_harmonicKernelScaled_mul_eq_of_harmonicOn hd
        hδsmooth.contDiffOn hδharm hε hεRδ)
  have hrepε :
      (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        harmonicMollify u ε) x = harmonicMollify u ε x := by
    simpa [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply] using
      (integral_harmonicKernelScaled_mul_eq_of_harmonicOn hd
        hεsmooth.contDiffOn hεharm hδ hδRε)
  have hg : LocallyIntegrable (Set.indicator (euclideanBall x₀ r) u.toFun) volume := by
    have hmem : MemLp (Set.indicator (euclideanBall x₀ r) u.toFun) 2 volume := by
      rw [memLp_indicator_iff_restrict hU.measurableSet]
      exact u.memL2
    exact hmem.locallyIntegrable (by norm_num)
  calc
    harmonicMollify u δ x =
        (harmonicKernelScaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          harmonicMollify u δ) x := hrepδ.symm
    _ = (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          harmonicMollify u ε) x := by
            exact harmonicScalarConvolution_double_comm
              (harmonicKernelScaled_hasCompactSupport hε)
              (harmonicKernelScaled_smooth ε).continuous
              (harmonicKernelScaled_hasCompactSupport hδ)
              (harmonicKernelScaled_smooth δ).continuous hg x
    _ = harmonicMollify u ε x := hrepε

end

end PDE
