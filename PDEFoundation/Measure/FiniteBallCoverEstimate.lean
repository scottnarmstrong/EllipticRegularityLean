module

public import PDEFoundation.Geometry.EuclideanBall.FiniteCover
public import PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Measure estimate for a finite family of balls with large averages

This is the finite covering bridge used in the weak estimate for the
Hardy--Littlewood maximal function.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The integral of a nonnegative integrable function over a finite disjoint
family of measurable sets is bounded by its integral over the whole space. -/
theorem sum_setIntegral_le_integral_of_pairwiseDisjoint
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) (s : Finset ι) (A : ι → Set α)
    (hf : Integrable f μ) (hnonneg : ∀ x, 0 ≤ f x)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hdisjoint : (s : Set ι).PairwiseDisjoint A) :
    ∑ i ∈ s, ∫ x in A i, f x ∂μ ≤ ∫ x, f x ∂μ := by
  rw [← integral_biUnion_finset s hA hdisjoint
    (fun i _ => hf.integrableOn)]
  exact setIntegral_le_integral hf (ae_of_all μ hnonneg)

/-- If every ball in a finite positive-radius family has average `|b|`
strictly larger than `t > 0`, then the union of the balls satisfies the
finite weak-type covering estimate with the exact triple-dilate factor. -/
theorem volume_iUnion_euclideanBall_toReal_le
    {d : ℕ} {ι : Type*} (s : Finset ι) (z : ι → Vec d) (r : ι → ℝ)
    (b : Vec d → ℝ) (t : ℝ)
    (hr : ∀ i ∈ s, 0 < r i) (ht : 0 < t)
    (hb : Integrable b volume)
    (havg : ∀ i ∈ s,
      t < ⨍ x in euclideanBall (z i) (r i), |b x| ∂volume) :
    (volume (⋃ i ∈ s, euclideanBall (z i) (r i))).toReal ≤
      (3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume := by
  classical
  obtain ⟨u, hus, hdisjoint, hcover⟩ :=
    exists_pairwiseDisjoint_euclideanBalls_covering_triples s z r hr
  have hunion :
      (⋃ i ∈ s, euclideanBall (z i) (r i)) ⊆
        ⋃ j ∈ u, euclideanBall (z j) (3 * r j) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact ⟨j, hj, hij hxi⟩
  have htriple_each (j : ι) (hj : j ∈ u) :
      volume (euclideanBall (z j) (3 * r j)) ≠ ⊤ := by
    exact
      volume_euclideanBall_ne_top (z j) (by
        have := hr j (hus hj)
        positivity)
  have htriple_top :
      (∑ j ∈ u, volume (euclideanBall (z j) (3 * r j))) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr htriple_each
  have hvolume :
      (volume (⋃ i ∈ s, euclideanBall (z i) (r i))).toReal ≤
        ∑ j ∈ u,
          (volume (euclideanBall (z j) (3 * r j))).toReal := by
    rw [← ENNReal.toReal_sum htriple_each]
    apply ENNReal.toReal_mono htriple_top
    exact (measure_mono hunion).trans
      (measure_biUnion_finset_le u fun j =>
        euclideanBall (z j) (3 * r j))
  have hscale (j : ι) (hj : j ∈ u) :
      (volume (euclideanBall (z j) (3 * r j))).toReal =
        (3 : ℝ) ^ d *
          (volume (euclideanBall (z j) (r j))).toReal := by
    have hrj := hr j (hus hj)
    rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos _ (by positivity),
      volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hrj]
    rw [mul_pow]
    ring
  have hball (j : ι) (hj : j ∈ u) :
      t * (volume (euclideanBall (z j) (r j))).toReal <
        ∫ x in euclideanBall (z j) (r j), |b x| ∂volume := by
    have havg_j := havg j (hus hj)
    rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ,
      measureReal_def] at havg_j
    have hvol := volume_euclideanBall_toReal_pos (z j) (hr j (hus hj))
    rw [mul_comm, ← div_eq_mul_inv] at havg_j
    exact (lt_div_iff₀ hvol).mp havg_j
  have hselected :
      t * ∑ j ∈ u, (volume (euclideanBall (z j) (r j))).toReal ≤
        ∫ x, |b x| ∂volume := by
    calc
      t * ∑ j ∈ u, (volume (euclideanBall (z j) (r j))).toReal =
          ∑ j ∈ u, t * (volume (euclideanBall (z j) (r j))).toReal := by
            rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ u,
          ∫ x in euclideanBall (z j) (r j), |b x| ∂volume :=
        Finset.sum_le_sum fun j hj => (hball j hj).le
      _ ≤ ∫ x, |b x| ∂volume :=
        sum_setIntegral_le_integral_of_pairwiseDisjoint
          (fun x => |b x|) u (fun j => euclideanBall (z j) (r j))
          hb.abs (fun x => abs_nonneg (b x))
          (fun j hj => isOpen_euclideanBall (z j) (r j) |>.measurableSet)
          hdisjoint
  calc
    (volume (⋃ i ∈ s, euclideanBall (z i) (r i))).toReal ≤
        ∑ j ∈ u, (volume (euclideanBall (z j) (3 * r j))).toReal := hvolume
    _ = (3 : ℝ) ^ d *
        ∑ j ∈ u, (volume (euclideanBall (z j) (r j))).toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hscale
    _ ≤ (3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume := by
      calc
        (3 : ℝ) ^ d *
            ∑ j ∈ u, (volume (euclideanBall (z j) (r j))).toReal =
            ((3 : ℝ) ^ d / t) *
              (t * ∑ j ∈ u,
                (volume (euclideanBall (z j) (r j))).toReal) := by
          field_simp [ht.ne']
        _ ≤ (3 : ℝ) ^ d / t * ∫ x, |b x| ∂volume :=
          mul_le_mul_of_nonneg_left hselected (div_nonneg (by positivity) ht.le)

end PDE
