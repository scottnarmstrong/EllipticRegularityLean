module

public import PDEFoundation.Ambient.MatrixPerturbation
public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.NormalizedLp

/-! # Literal zero extensions of coefficient perturbations -/

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- Every matrix entry difference is controlled by the Euclidean operator bound. -/
theorem IsMatrixPerturbationLE.abs_entry_sub_le {d : ℕ}
    {delta : ℝ} {A B : Mat d} (h : IsMatrixPerturbationLE delta A B)
    (i j : Fin d) : |(A-B) i j| ≤ delta := by
  have hh := (abs_apply_le_vecEuclideanNorm (matVecMul (A-B) (basisVec j)) i).trans
    (h (basisVec j))
  have heq : matVecMul (A-B) (basisVec j) i = (A-B) i j := by
    classical
    unfold matVecMul basisVec
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, mul_one]
    · intro k _ hkj
      simp only [Pi.single_eq_of_ne hkj, mul_zero]
    · simp
  rw [heq, vecEuclideanNorm_basisVec, mul_one] at hh
  exact hh

/-- Every entry of the literal zero extension of an identity perturbation
belongs to every extended `Lᵖ` space on a finite-volume domain. -/
theorem memLp_indicator_matrix_sub_identity_entry {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUtop : volume U ≠ ⊤)
    (a : CoeffField d) {delta : ℝ} (_hdelta : 0 ≤ delta)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE delta (a x) (1:Mat d))
    (i j : Fin d) (p : ENNReal) :
    MemLp (U.indicator (fun x => (a x - 1) i j)) p volume := by
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_restrict.mpr hUtop
  rw [memLp_indicator_iff_restrict hU]
  apply MemLp.of_bound ((ha i j).aestronglyMeasurable.sub aestronglyMeasurable_const) delta
  filter_upwards [hclose] with x hx
  exact hx.abs_entry_sub_le i j

/-- Extending the perturbation by zero preserves the same identity-distance
bound on the whole space. -/
theorem ae_matrix_identity_add_indicator_perturbation {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U) (a : CoeffField d)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hclose : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE delta (a x) (1:Mat d)) :
    ∀ᵐ x ∂volume, IsMatrixPerturbationLE delta
      ((1:Mat d) + U.indicator (fun y => a y - 1) x) (1:Mat d) := by
  have hglobal : ∀ᵐ x ∂volume, x ∈ U →
      IsMatrixPerturbationLE delta (a x) (1:Mat d) :=
    (ae_restrict_iff' hU).mp hclose
  filter_upwards [hglobal] with x hx
  by_cases hxU : x ∈ U
  · simpa only [Set.indicator_of_mem hxU, add_sub_cancel] using hx hxU
  · intro ξ
    simp only [Set.indicator_of_notMem hxU, add_zero, sub_self]
    change vecEuclideanNorm ((0:Mat d).mulVec ξ) ≤ delta*vecEuclideanNorm ξ
    simpa only [Matrix.zero_mulVec, vecEuclideanNorm, vecNormSq, vecDot,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, Real.sqrt_zero] using
      mul_nonneg hdelta (vecEuclideanNorm_nonneg ξ)

end PDE
