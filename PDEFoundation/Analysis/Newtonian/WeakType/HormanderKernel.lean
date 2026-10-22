module

public import PDEFoundation.Ambient.Matrix
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.EuclideanVectorIntegral
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # Pointwise Hörmander bound for an abstract kernel

For an abstract kernel `K : Vec d → Mat d` with the Hölder property in the Euclidean operator
norm (the shape of the Hölder bound for the Newtonian kernel), the integral
`∫ (K (x - y) - K (x - c)) b y dy` is bounded, for `|x - c| ≥ 2 r` and `b` supported in
`|y - c| ≤ r`, by `A r |x - c|^{-(d+1)} ‖b‖₁`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- The Hölder property of a matrix kernel in the Euclidean operator norm:
`|K z - K z'| ≤ A |z - z'| / |z|^{d+1}` whenever `|z - z'| ≤ |z| / 2`. -/
def KernelHolder (d : ℕ) (K : Vec d → Mat d) (A : ℝ) : Prop :=
  ∀ z z' : Vec d, z ≠ 0 →
    vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2 →
    ∀ v : Vec d,
      vecEuclideanNorm (matVecMul (K z - K z') v) ≤
        A * (vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1)) * vecEuclideanNorm v

theorem matVecMul_neg' (M : Mat d) (v : Vec d) : matVecMul (-M) v = -matVecMul M v := by
  ext i
  simp [matVecMul, Finset.sum_neg_distrib]

theorem matVecMul_zero_right (M : Mat d) : matVecMul M 0 = 0 := by
  ext i
  simp [matVecMul]

theorem vecEuclideanNorm_single_one (j : Fin d) : vecEuclideanNorm (Pi.single j (1 : ℝ)) = 1 := by
  unfold vecEuclideanNorm
  rw [vecNormSq_eq_sum_sq]
  simp [Pi.single_apply]

/-- A Hölder kernel is continuous away from the origin, entrywise. -/
theorem KernelHolder.continuousAt_entry {K : Vec d → Mat d} {A : ℝ} (hK : KernelHolder d K A)
    {z0 : Vec d} (hz0 : z0 ≠ 0) (i j : Fin d) :
    ContinuousAt (fun z => K z i j) z0 := by
  have hn0 : 0 < vecEuclideanNorm z0 := vecEuclideanNorm_pos_iff.mpr hz0
  have hlim : Tendsto (fun z : Vec d => vecEuclideanNorm (z0 - z)) (𝓝 z0) (𝓝 0) := by
    have hc : Continuous (fun z : Vec d => vecEuclideanNorm (z0 - z)) :=
      (continuous_vecEuclideanNorm (d := d)).comp (continuous_const.sub continuous_id)
    have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.mpr rfl
    simpa [h0] using hc.tendsto z0
  have hev : ∀ᶠ z in 𝓝 z0, vecEuclideanNorm (z0 - z) ≤ vecEuclideanNorm z0 / 2 :=
    hlim.eventually (ge_mem_nhds (by positivity))
  have hbound : Tendsto (fun z : Vec d => A * (vecEuclideanNorm (z0 - z) /
      vecEuclideanNorm z0 ^ (d + 1)) * 1) (𝓝 z0) (𝓝 0) := by
    have := ((hlim.div_const (vecEuclideanNorm z0 ^ (d + 1))).const_mul A).mul_const (1 : ℝ)
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hev] with z hz
  have h1 := hK z0 z hz0 hz (Pi.single j 1)
  rw [vecEuclideanNorm_single_one] at h1
  have h2 : |(K z0 - K z) i j| ≤ vecEuclideanNorm (matVecMul (K z0 - K z) (Pi.single j 1)) := by
    refine le_trans (le_of_eq ?_) (abs_apply_le_vecEuclideanNorm _ i)
    simp [matVecMul, Pi.single_apply]
  have h3 : ‖K z i j - K z0 i j‖ = |(K z0 - K z) i j| := by
    rw [Real.norm_eq_abs, ← abs_neg]
    simp
  rw [norm_norm, h3]
  exact h2.trans h1

/-- The entries of a Hölder kernel, composed with `x - ·`, are a.e. strongly measurable. -/
theorem KernelHolder.aestronglyMeasurable_entry [NeZero d] {K : Vec d → Mat d} {A : ℝ}
    (hK : KernelHolder d K A) (x : Vec d) (i j : Fin d) :
    AEStronglyMeasurable (fun y => K (x - y) i j) volume := by
  have hcont : ContinuousOn (fun y : Vec d => K (x - y) i j) ({x}ᶜ) := by
    intro y hy
    have hne : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hy (by simp [h]))
    exact ((hK.continuousAt_entry hne i j).comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have := hcont.aestronglyMeasurable (μ := (volume : Measure (Vec d)))
    (measurableSet_singleton x).compl
  rwa [restrict_compl_singleton] at this

end

end PDE.NewtonWeakType
