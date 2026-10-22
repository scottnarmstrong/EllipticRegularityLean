module

public import PDEFoundation.PDE.HarmonicReproductionRadial
public import Mathlib.Analysis.Convolution

/-! # Convolution form of local harmonic reproduction -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Convolution

noncomputable section

variable {d : ℕ}

/-- On the interior ball, convolution with the zero extension reproduces a
smooth harmonic function. -/
theorem harmonicKernelScaled_convolution_indicator_eq_of_harmonicOn
    (hd : 0 < d) {v : Vec d → ℝ} {x : Vec d} {R s : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ y ∈ euclideanBall x R, euclideanCoordLaplacian v y = 0)
    (hs : 0 < s) (hsR : s < R)
    {x' : Vec d} (hx' : x' ∈ euclideanBall x (R - s)) :
    (harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator (euclideanBall x R) v) x' = v x' := by
  have hmargin : 0 < R - s := by linarith
  have hdist := (mem_euclideanBall_iff_vecEuclideanNorm_lt hmargin).mp hx'
  have hR : 0 < R := hs.trans hsR
  have hsubset : euclideanBall x' s ⊆ euclideanBall x R :=
    euclideanBall_subset_of_center_norm_add_le hs hR (by linarith)
  have hpoint (y : Vec d) :
      harmonicKernelScaled s y * Set.indicator (euclideanBall x R) v (x' - y) =
        harmonicKernelScaled s y * v (x' - y) := by
    by_cases hk : harmonicKernelScaled s y = 0
    · simp [hk]
    · have hy' : y ∈ tsupport (harmonicKernelScaled s) :=
        subset_tsupport _ (Function.mem_support.mpr hk)
      have hy : y ∈ euclideanBall (0 : Vec d) s :=
        (harmonicKernelScaled_tsupport_subset hs) hy'
      have hxy : x' - y ∈ euclideanBall x' s := by
        have hsub : (x' - y) - x' = -(y - (0 : Vec d)) := by abel
        change euclideanSqDist (x' - y) x' < s ^ 2
        change euclideanSqDist y (0 : Vec d) < s ^ 2 at hy
        simpa only [euclideanSqDist, hsub, vecNormSq_neg] using hy
      rw [Set.indicator_of_mem (hsubset hxy)]
  rw [show (harmonicKernelScaled s ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator (euclideanBall x R) v) x' =
      ∫ y, harmonicKernelScaled s y *
        Set.indicator (euclideanBall x R) v (x' - y) ∂volume by
          simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
            smul_eq_mul]]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact integral_harmonicKernelScaled_mul_eq_on_innerBall hd hv hharm hs hsR hx'

end

end PDE
