module

public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Measure.NormalizedLpTendsto
public import PDEFoundation.Measure.EuclideanFieldLpConvergence

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

private theorem memLp_vecEuclideanNorm_of_coordinate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {p : ℝ≥0∞} {g : α → Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) p μ) :
    MemLp (fun x => vecEuclideanNorm (g x)) p μ := by
  have hHilbert : MemLp (fun x => (g x).toHilbertVec) p μ := by
    rw [memLp_piLp_iff]
    exact hg
  exact hHilbert.norm.ae_eq (Eventually.of_forall fun x =>
    Vec.vecEuclideanNorm_eq_norm_toHilbertVec (g x) |>.symm)

private theorem abs_vecEuclideanNorm_sub_le
    {d : ℕ} (x y : Vec d) :
    |vecEuclideanNorm x - vecEuclideanNorm y| ≤
      vecEuclideanNorm (x - y) := by
  have hxy : vecEuclideanNorm x ≤
      vecEuclideanNorm (x - y) + vecEuclideanNorm y := by
    simpa only [sub_add_cancel] using vecEuclideanNorm_add_le (x - y) y
  have hyx : vecEuclideanNorm y ≤
      vecEuclideanNorm (x - y) + vecEuclideanNorm x := by
    have h := vecEuclideanNorm_add_le (y - x) x
    rw [vecEuclideanNorm_sub_comm y x] at h
    simpa only [sub_add_cancel] using h
  rw [abs_le]
  constructor <;> linarith only [hxy, hyx]

/-- Strong convergence of native vector fields in their Euclidean magnitude
implies strong convergence of the corresponding scalar magnitudes. -/
theorem tendsto_eLpNorm_vecEuclideanNorm_sub_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {p : ℝ≥0∞}
    {gSeq : ℕ → α → Vec d} {g : α → Vec d}
    (hconv : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (gSeq n x - g x)) p μ)
      atTop (𝓝 0))
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun x => vecEuclideanNorm (gSeq n x) - vecEuclideanNorm (g x)) μ) :
    Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (gSeq n x) - vecEuclideanNorm (g x)) p μ)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      eLpNorm
          (fun x => vecEuclideanNorm (gSeq n x) - vecEuclideanNorm (g x))
          p μ ≤
        eLpNorm (fun x => vecEuclideanNorm (gSeq n x - g x)) p μ := by
    apply eLpNorm_mono_ae (hmeas n)
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg _)]
    exact abs_vecEuclideanNorm_sub_le _ _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hconv ?_ ?_
  · exact fun _ => bot_le
  · exact hbound

/-- Strong convergence of native vector fields in Euclidean-magnitude
Lp implies convergence of their scalar Euclidean-magnitude seminorms. -/
theorem tendsto_eLpNorm_vecEuclideanNorm_of_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {gSeq : ℕ → α → Vec d} {g : α → Vec d}
    (hgSeq : ∀ n i, MemLp (fun x => gSeq n x i) p μ)
    (hg : ∀ i, MemLp (fun x => g x i) p μ)
    (hconv : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (gSeq n x - g x)) p μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => vecEuclideanNorm (gSeq n x)) p μ)
      atTop (𝓝 (eLpNorm (fun x => vecEuclideanNorm (g x)) p μ)) := by
  have hSeqMag := fun n => memLp_vecEuclideanNorm_of_coordinate (hgSeq n)
  have hgMag := memLp_vecEuclideanNorm_of_coordinate hg
  apply tendsto_eLpNorm_of_tendsto_sub hp
      (fun n => (hSeqMag n).aestronglyMeasurable)
      hgMag.aestronglyMeasurable hgMag.eLpNorm_ne_top
  exact tendsto_eLpNorm_vecEuclideanNorm_sub_zero hconv fun n =>
    (hSeqMag n).aestronglyMeasurable.sub hgMag.aestronglyMeasurable

/-- On a positive finite-volume set, strong convergence in the unnormalized
Euclidean-magnitude seminorm implies convergence of the exact real normalized
Euclidean-magnitude seminorms. -/
theorem tendsto_toReal_euclideanFieldELpMeanNormOn_of_sub
    {d m : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    {gSeq : ℕ → Vec d → Vec m} {g : Vec d → Vec m}
    (hgSeq : ∀ n i, MemLp (fun x => gSeq n x i) p (volumeOn U))
    (hg : ∀ i, MemLp (fun x => g x i) p (volumeOn U))
    (hconv : Tendsto (fun n => eLpNorm
      (fun x => vecEuclideanNorm (gSeq n x - g x)) p (volumeOn U))
      atTop (𝓝 0)) :
    Tendsto (fun n =>
      (eLpMeanNormOn U p (fun x => vecEuclideanNorm (gSeq n x))).toReal)
      atTop
      (𝓝 (eLpMeanNormOn U p (fun x => vecEuclideanNorm (g x))).toReal) := by
  have hgSeqMag (n : ℕ) :=
    memLp_vecEuclideanNorm_of_coordinate (hgSeq n)
  have hgMag := memLp_vecEuclideanNorm_of_coordinate hg
  have hgSeqMagMean (n : ℕ) :=
    memLp_normalizedVolumeOn_of_memLpOn (hgSeqMag n) hUPos
  have hgMagMean :=
    memLp_normalizedVolumeOn_of_memLpOn hgMag hUPos
  have hscalar :=
    tendsto_eLpNorm_vecEuclideanNorm_sub_zero hconv fun n =>
      (hgSeqMag n).aestronglyMeasurable.sub hgMag.aestronglyMeasurable
  have hconvMean : Tendsto (fun n => eLpMeanNormOn U p
      ((fun x => vecEuclideanNorm (gSeq n x)) -
        fun x => vecEuclideanNorm (g x))) atTop (𝓝 0) := by
    exact tendsto_eLpMeanNormOn_sub_zero_of_tendsto_eLpNormOn_sub_zero
      hUPos hUTop hscalar
  have hnorm := tendsto_eLpNorm_of_tendsto_sub hp
    (fun n => (hgSeqMagMean n).aestronglyMeasurable)
    hgMagMean.aestronglyMeasurable hgMagMean.eLpNorm_ne_top hconvMean
  exact (ENNReal.tendsto_toReal hgMagMean.eLpNorm_ne_top).comp hnorm

end PDE
