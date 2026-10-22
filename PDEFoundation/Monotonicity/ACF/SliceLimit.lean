module

public import PDEFoundation.Monotonicity.ACF.SlicePolar
public import PDEFoundation.Monotonicity.ACF.SliceL2
public import PDEFoundation.Geometry.ConvexDomain

/-!
# ACF-S2: slice limits along `L²`-convergent sequences

If `pₙ → p` in `L²(B_R)` then, along a subsequence, the slice integrals of `pₙ²` converge to the
slice integral of `p²` for almost every `r ∈ (0, R)`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

theorem slice_indicator_ball {R r : ℝ} (hr : r ∈ Ioo 0 R) (f : Vec d → ℝ) :
    (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      (euclideanBall (0 : Vec d) R).indicator f (r • (ω : HilbertVec d).toVec)) =
    fun ω : Metric.sphere (0 : HilbertVec d) 1 => f (r • (ω : HilbertVec d).toVec) := by
  funext ω
  refine indicator_of_mem ?_ _
  rw [mem_euclideanBall_zero_iff, vecNormSq_smul, BallDivergence.vecNormSq_toVec,
    mem_sphere_zero_iff_norm.1 ω.2]
  nlinarith [hr.1, hr.2]

theorem SliceIntegrable.indicator_ball_iff {R r : ℝ} (hr : r ∈ Ioo 0 R) (f : Vec d → ℝ) :
    SliceIntegrable ((euclideanBall (0 : Vec d) R).indicator f) r ↔ SliceIntegrable f r := by
  unfold SliceIntegrable
  rw [slice_indicator_ball hr]

theorem sliceIntegral_indicator_ball {R r : ℝ} (hr : r ∈ Ioo 0 R) (f : Vec d → ℝ) :
    sliceIntegral ((euclideanBall (0 : Vec d) R).indicator f) r = sliceIntegral f r := by
  rw [sliceIntegral_eq, sliceIntegral_eq, slice_indicator_ball hr]

theorem measurableSet_euclideanBall_zero (R : ℝ) :
    MeasurableSet (euclideanBall (0 : Vec d) R) :=
  (isOpen_euclideanBall (0 : Vec d) R).measurableSet

/-- Along a subsequence, slice integrals of squares of an `L²(B_R)`-convergent sequence converge
for a.e. radius `r ∈ (0, R)`. -/
theorem exists_subseq_sliceIntegral_sq [NeZero d] {R : ℝ} {pn : ℕ → Vec d → ℝ} {p : Vec d → ℝ}
    (hpm : AEStronglyMeasurable p (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hpnm : ∀ n, AEStronglyMeasurable (pn n) (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hp2 : Integrable (fun x => p x ^ 2) (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hpn2 : ∀ n, Integrable (fun x => pn n x ^ 2)
      (volume.restrict (euclideanBall (0 : Vec d) R)))
    (h : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R, (pn n x - p x) ^ 2) atTop
      (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => p x ^ 2) r ∧
      (∀ k, SliceIntegrable (fun x => pn (φ k) x ^ 2) r) ∧
      Tendsto (fun k => sliceIntegral (fun x => pn (φ k) x ^ 2) r) atTop
        (nhds (sliceIntegral (fun x => p x ^ 2) r)) := by
  set B := euclideanBall (0 : Vec d) R with hBdef
  have hB : MeasurableSet B := measurableSet_euclideanBall_zero R
  have he : ∀ n, Integrable (fun x => (pn n x - p x) ^ 2) (volume.restrict B) := by
    intro n
    refine Integrable.mono' (((hpn2 n).const_mul 2).add (hp2.const_mul 2)) 
      (((hpnm n).sub hpm).pow 2) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (pn n x + p x)]
  have hL1 := tendsto_integral_abs_sq_sub hp2 he h
  have hGn : ∀ n, Integrable (B.indicator fun x => pn n x ^ 2) :=
    fun n => (integrable_indicator_iff hB).2 (hpn2 n)
  have hG : Integrable (B.indicator fun x => p x ^ 2) := (integrable_indicator_iff hB).2 hp2
  have hconv : Tendsto (fun n => ∫ x, |B.indicator (fun x => pn n x ^ 2) x -
      B.indicator (fun x => p x ^ 2) x|) atTop (nhds 0) := by
    refine hL1.congr fun n => ?_
    rw [← integral_indicator hB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ B <;> simp [indicator, hx]
  obtain ⟨φ, hφ, hae⟩ := exists_subseq_sliceIntegral_tendsto hGn hG hconv
  refine ⟨φ, hφ, ?_⟩
  have hae' := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) R ⊆ Ioi (0 : ℝ)) hae
  have hmem : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), r ∈ Ioo (0 : ℝ) R :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hae', hmem] with r ⟨h1, h2, h3⟩ hr
  refine ⟨(SliceIntegrable.indicator_ball_iff hr _).1 h1,
    fun k => (SliceIntegrable.indicator_ball_iff hr _).1 (h2 k), ?_⟩
  rw [hBdef] at h3
  simpa only [sliceIntegral_indicator_ball hr] using h3

/-- Variant of `exists_subseq_sliceIntegral_sq` with the square-integrability data derived from
pointwise domination by integrable functions. -/
theorem exists_subseq_sliceIntegral_sq_of_dom [NeZero d] {R : ℝ} {pn : ℕ → Vec d → ℝ}
    {p : Vec d → ℝ} {S : Vec d → ℝ} {Sn Dn : ℕ → Vec d → ℝ}
    (hpm : AEStronglyMeasurable p (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hpnm : ∀ n, AEStronglyMeasurable (pn n) (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hS : Integrable S (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hSn : ∀ n, Integrable (Sn n) (volume.restrict (euclideanBall (0 : Vec d) R)))
    (hDn : ∀ n, Integrable (Dn n) (volume.restrict (euclideanBall (0 : Vec d) R)))
    (h1 : ∀ x, p x ^ 2 ≤ S x) (h2 : ∀ n x, pn n x ^ 2 ≤ Sn n x)
    (h3 : ∀ n x, (pn n x - p x) ^ 2 ≤ Dn n x)
    (hD : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R, Dn n x) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => p x ^ 2) r ∧
      (∀ k, SliceIntegrable (fun x => pn (φ k) x ^ 2) r) ∧
      Tendsto (fun k => sliceIntegral (fun x => pn (φ k) x ^ 2) r) atTop
        (nhds (sliceIntegral (fun x => p x ^ 2) r)) := by
  have hp2 : Integrable (fun x => p x ^ 2) (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    hS.mono' (hpm.pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h1 x)
  have hpn2 : ∀ n, Integrable (fun x => pn n x ^ 2)
      (volume.restrict (euclideanBall (0 : Vec d) R)) := fun n =>
    (hSn n).mono' ((hpnm n).pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h2 n x)
  have hen : ∀ n, Integrable (fun x => (pn n x - p x) ^ 2)
      (volume.restrict (euclideanBall (0 : Vec d) R)) := fun n =>
    (hDn n).mono' (((hpnm n).sub hpm).pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h3 n x)
  refine exists_subseq_sliceIntegral_sq hpm hpnm hp2 hpn2 ?_
  refine squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) (fun n => ?_) hD
  exact integral_mono (hen n) (hDn n) (h3 n)

end

end PDE
