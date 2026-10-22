module

public import PDEFoundation.PDE.HarmonicTestedEquation
public import PDEFoundation.PDE.HarmonicKernel
public import Mathlib.Analysis.Convolution

/-!
# Mollification of weakly harmonic functions

The normalized round kernel regularizes the zero extension of an `H¹` function.
On interior balls, weak harmonicity makes each regularization classically
harmonic. The scaled kernels also converge as an approximate identity on
continuous test functions.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Convolution

noncomputable section

namespace PDE

variable {d : ℕ}

/-- Convolution of an `H¹(U)` representative's zero extension with the
normalized round kernel of radius `δ`. -/
def harmonicMollify {U : Set (Vec d)} (u : H1Function U) (δ : ℝ) : Vec d → ℝ :=
  harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    Set.indicator U u.toFun

/-- The zero extension of an `H¹` function on an open set is locally
integrable, which makes its harmonic mollification smooth. -/
theorem contDiff_harmonicMollify {U : Set (Vec d)} (hU : IsOpen U)
    (u : H1Function U) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicMollify u δ) := by
  unfold harmonicMollify
  have hmem : MemLp (Set.indicator U u.toFun) 2 volume := by
    rw [memLp_indicator_iff_restrict hU.measurableSet]
    exact u.memL2
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (harmonicKernelScaled_hasCompactSupport hδ)
    (harmonicKernelScaled_smooth δ) (hmem.locallyIntegrable (by norm_num))

/-- Reflection of the scaled kernel is supported inside the Euclidean ball of
radius `δ` about its evaluation point. -/
theorem tsupport_reflected_harmonicKernelScaled_subset {x : Vec d} {δ : ℝ}
    (hδ : 0 < δ) :
    tsupport (fun y : Vec d => harmonicKernelScaled δ (x - y)) ⊆
      euclideanBall x δ := by
  have hcomp : (fun y : Vec d => harmonicKernelScaled δ (x - y)) =
      harmonicKernelScaled δ ∘ Homeomorph.subLeft x := by
    rfl
  rw [hcomp, tsupport_comp_eq_preimage]
  intro y hy
  have hy' : x - y ∈ tsupport (harmonicKernelScaled δ) := by
    change Homeomorph.subLeft x y ∈ tsupport (harmonicKernelScaled δ) at hy
    simpa [Homeomorph.subLeft] using hy
  have hyball : x - y ∈ euclideanBall 0 δ :=
    harmonicKernelScaled_tsupport_subset hδ hy'
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).2
  have hz := (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hyball
  have hneg : y - x = -(x - y) := by abel
  rw [hneg, vecEuclideanNorm_neg]
  simpa only [sub_zero] using hz

/-- A weak identity-coefficient solution becomes classically harmonic wherever
the radius-`δ` Euclidean ball stays in its domain. -/
theorem euclideanCoordLaplacian_harmonicMollify_eq_zero
    {U : Set (Vec d)} (hU : IsOpen U) (u : H1Function U)
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) U u 0 0)
    {x : Vec d} {δ : ℝ} (hδ : 0 < δ)
    (hball : euclideanBall x δ ⊆ U) :
    euclideanCoordLaplacian (harmonicMollify u δ) x = 0 := by
  unfold harmonicMollify
  apply euclideanCoordLaplacian_convolution_indicator_eq_zero hU
    (fun φ => hsol.identityCoefficient_test_eq_zero φ)
    (harmonicKernelScaled_hasCompactSupport hδ)
    (harmonicKernelScaled_smooth δ) x
  exact (tsupport_reflected_harmonicKernelScaled_subset hδ).trans hball

/-- Interior-ball specialization of `euclideanCoordLaplacian_harmonicMollify_eq_zero`.
The gap `δ` between the evaluation point and the boundary is measured using
round Euclidean balls on `Vec d`. -/
theorem euclideanCoordLaplacian_harmonicMollify_ball_eq_zero
    {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r)
    (u : H1Function (euclideanBall (0 : Vec d) r))
    (hsol : IsWeakDivergenceFormSolutionOn
      (fun _ : Vec d => (1 : Mat d)) (euclideanBall 0 r) u 0 0)
    {x : Vec d} (hx : x ∈ euclideanBall 0 (r - δ)) :
    euclideanCoordLaplacian (harmonicMollify u δ) x = 0 := by
  apply euclideanCoordLaplacian_harmonicMollify_eq_zero
    (isOpen_euclideanBall 0 r) u hsol hδ
  have hr : 0 < r := lt_trans hδ hδr
  have hxnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt (sub_pos.mpr hδr)).1 hx
  intro y hy
  have hynorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
  have hdecomp : y - (0 : Vec d) = (y - x) + (x - 0) := by abel
  rw [hdecomp]
  calc
    vecEuclideanNorm ((y - x) + (x - 0)) ≤
        vecEuclideanNorm (y - x) + vecEuclideanNorm (x - 0) :=
      vecEuclideanNorm_add_le _ _
    _ < δ + (r - δ) := add_lt_add hynorm hxnorm
    _ = r := by ring

/-- The pointwise integral convention for `harmonicMollify`. -/
theorem harmonicMollify_eq_integral {U : Set (Vec d)} (u : H1Function U)
    (δ : ℝ) (x : Vec d) :
    harmonicMollify u δ x =
      ∫ y, harmonicKernelScaled δ y * Set.indicator U u.toFun (x - y) := by
  simp [harmonicMollify, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply]

/-- Equality of representatives on the Euclidean `δ`-ball implies equality of
their mollifications at its center. -/
theorem harmonicMollify_congr_on_ball {U : Set (Vec d)}
    {u v : H1Function U} {x : Vec d} {δ : ℝ} (hδ : 0 < δ)
    (huv : ∀ y ∈ euclideanBall x δ, u.toFun y = v.toFun y) :
    harmonicMollify u δ x = harmonicMollify v δ x := by
  rw [harmonicMollify_eq_integral, harmonicMollify_eq_integral]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : harmonicKernelScaled δ y = 0
  · simp [hy]
  · have hy' : y ∈ tsupport (harmonicKernelScaled δ) :=
      subset_tsupport _ (Function.mem_support.mpr hy)
    have hyball : y ∈ euclideanBall 0 δ :=
      (harmonicKernelScaled_tsupport_subset hδ) hy'
    have hxy : x - y ∈ euclideanBall x δ := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).2
      have hnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hyball
      have hsub : (x - y) - x = -y := by abel
      rw [hsub, vecEuclideanNorm_neg]
      simpa only [sub_zero] using hnorm
    by_cases hU : x - y ∈ U
    · simp [hU, huv (x - y) hxy]
    · simp [hU]

/-- The radial profile makes every scaled harmonic kernel even. -/
theorem harmonicKernelScaled_neg {δ : ℝ} (y : Vec d) :
    harmonicKernelScaled δ (-y) = harmonicKernelScaled δ y := by
  rw [harmonicKernelScaled_eq_profile, harmonicKernelScaled_eq_profile]
  congr 1
  simp [vecNormSq, vecDot]

private theorem support_harmonicKernelScaled_subset_metric_ball
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) :
    Function.support (harmonicKernelScaled δ) ⊆ Metric.ball (0 : Vec d) ε := by
  intro y hy
  have hts : y ∈ tsupport (harmonicKernelScaled δ) :=
    subset_tsupport _ hy
  have heuc := (mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1
    (harmonicKernelScaled_tsupport_subset hδ hts)
  rw [sub_zero] at heuc
  rw [Metric.mem_ball, dist_zero_right]
  exact (norm_le_vecEuclideanNorm y).trans_lt (heuc.trans hδε)

/-- The scaled harmonic kernels form an approximate identity on continuous
functions: convolution tends pointwise to the input from positive scales. -/
theorem harmonicKernelScaled_convolution_tendsto_right
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (x : Vec d) :
    Tendsto
      (fun δ : ℝ =>
        (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ψ x)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hsmall : Tendsto (fun δ : ℝ => Function.support (harmonicKernelScaled δ))
      l (nhds (0 : Vec d)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro s hs
    rcases Metric.mem_nhds_iff.1 hs with ⟨ε, hε, hball⟩
    have hδevent : ∀ᶠ δ in l, δ < ε := by
      exact (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds hε)
    filter_upwards [hδevent, self_mem_nhdsWithin] with δ hδε hδ
    exact (support_harmonicKernelScaled_subset_metric_ball hδ hδε).trans hball
  have hnonneg : ∀ᶠ δ in l, ∀ y : Vec d, 0 ≤ harmonicKernelScaled δ y := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ y
    exact harmonicKernelScaled_nonneg (d := d) hδ y
  have hint : ∀ᶠ δ in l,
      (∫ (y : Vec d), harmonicKernelScaled (d := d) δ y ∂volume) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact harmonicKernelScaled_integral_eq_one (d := d) hδ
  have hmeas : ∀ᶠ δ in l,
      AEStronglyMeasurable ψ volume := Eventually.of_forall fun _ =>
        hψ.aestronglyMeasurable
  have hjoint : Tendsto (Function.uncurry (fun (_ : ℝ) (y : Vec d) => ψ y))
      (l ×ˢ nhds x) (nhds (ψ x)) := by
    change Tendsto (fun p : ℝ × Vec d => ψ p.2) (l ×ˢ nhds x) (nhds (ψ x))
    exact (hψ.tendsto x).comp tendsto_snd
  have hindex : Tendsto (fun _ : ℝ => x) l (nhds x) := tendsto_const_nhds
  simpa [l] using
    (MeasureTheory.convolution_tendsto_right
      (μ := volume)
      (hnφ := hnonneg) (hiφ := hint) (hφ := hsmall)
      (hmg := hmeas) (hcg := hjoint) (hk := hindex))

end PDE

end
