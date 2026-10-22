module

public import PDEFoundation.Ambient.MatrixPerturbation
public import PDEFoundation.PDE.CoefficientL2

/-!
# `L²` fluxes of coefficients close to the identity

An almost everywhere Euclidean operator bound on `a - I` controls its flux
with the same constant `delta`. The full coefficient action is controlled by
`1 + delta`. Coefficient fields remain the existing native `CoeffField`; only
the source-specific closeness hypothesis is added here.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- Matrix action on a coordinate basis vector reads the corresponding
matrix entry. -/
private theorem matVecMul_basisVec_apply {d : ℕ} (A : Mat d)
    (i j : Fin d) :
    matVecMul A (basisVec j) i = A i j := by
  unfold matVecMul basisVec
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, mul_one]
  · intro k _hk hkj
    simp only [Pi.single_eq_of_ne hkj, mul_zero]
  · simp

/-- An almost everywhere Euclidean operator bound for `a - I` controls every
matrix entry of the perturbation by the same constant. -/
theorem ae_abs_matrix_sub_identity_entry_le_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {delta : ℝ}
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    ∀ᵐ x ∂volumeOn U, ∀ i j, |(a x - 1) i j| ≤ delta := by
  filter_upwards [hclose] with x hx
  intro i j
  calc
    |(a x - 1) i j| =
        |matVecMul (a x - 1) (basisVec j) i| := by
          rw [matVecMul_basisVec_apply]
    _ ≤ vecEuclideanNorm (matVecMul (a x - 1) (basisVec j)) :=
      abs_apply_le_vecEuclideanNorm _ _
    _ ≤ delta * vecEuclideanNorm (basisVec j) := hx (basisVec j)
    _ = delta := by rw [vecEuclideanNorm_basisVec, mul_one]

/-- The full coefficient has the corresponding almost everywhere entry bound
`1 + delta`. -/
theorem ae_abs_matrix_entry_le_one_add_delta_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {delta : ℝ}
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    ∀ᵐ x ∂volumeOn U, ∀ i j, |a x i j| ≤ 1 + delta := by
  filter_upwards [ae_abs_matrix_sub_identity_entry_le_of_isMatrixPerturbationLE
    hclose] with x hx
  intro i j
  have hsplit : a x i j = (a x - 1) i j + (1 : Mat d) i j := by
    simp only [Matrix.sub_apply]
    ring
  have hone : |(1 : Mat d) i j| ≤ 1 := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  calc
    |a x i j| = |(a x - 1) i j + (1 : Mat d) i j| := by rw [hsplit]
    _ ≤ |(a x - 1) i j| + |(1 : Mat d) i j| := abs_add_le _ _
    _ ≤ delta + 1 := add_le_add (hx i j) hone
    _ = 1 + delta := by ring

/-- The almost everywhere perturbation bound controls the Euclidean norm of
its flux by `delta`. -/
theorem ae_vecEuclideanNorm_matVecMul_sub_identity_le_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {G : Vec d → Vec d}
    {delta : ℝ}
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    ∀ᵐ x ∂volumeOn U,
      vecEuclideanNorm (matVecMul (a x - 1) (G x)) ≤
        delta * vecEuclideanNorm (G x) := by
  filter_upwards [hclose] with x hx
  exact hx (G x)

/-- The same hypothesis bounds the full coefficient flux by `1 + delta` in
the explicit Euclidean norm. -/
theorem ae_vecEuclideanNorm_matVecMul_le_one_add_delta_mul_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {G : Vec d → Vec d}
    {delta : ℝ}
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) :
    ∀ᵐ x ∂volumeOn U,
      vecEuclideanNorm (matVecMul (a x) (G x)) ≤
        (1 + delta) * vecEuclideanNorm (G x) := by
  filter_upwards [hclose] with x hx
  exact vecEuclideanNorm_matVecMul_le_one_add_delta_mul_of_isMatrixPerturbationLE
    hx (G x)

private theorem aemeasurable_sub_identity
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U)) :
    ∀ i j, AEMeasurable (fun x => (a x - (1 : Mat d)) i j) (volumeOn U) := by
  intro i j
  exact (ha i j).sub aemeasurable_const

/-- A measurable coefficient field satisfying an almost everywhere operator
bound from the identity sends native-vector `L²(U)` fields through `a - I`
into native-vector `L²(U)`. -/
theorem memVectorL2On_matVecMul_sub_identity_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {G : Vec d → Vec d}
    {delta : ℝ}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hG : MemVectorL2On U G) :
    MemVectorL2On U (fun x => matVecMul (a x - 1) (G x)) := by
  classical
  intro i
  have hsum : MemLpOn U (2 : ℝ≥0∞)
      (fun x => ∑ j : Fin d, (a x - 1) i j * G x j) := by
    refine MeasureTheory.memLp_finsetSum
      (s := Finset.univ)
      (f := fun j : Fin d => fun x : Vec d => (a x - 1) i j * G x j) ?_
    intro j _hj
    have hGj : MemLpOn U (2 : ℝ≥0∞) (fun x => G x j) := hG j
    have hcoeff : AEMeasurable
        (fun x => (a x - 1) i j) (volumeOn U) := by
      exact aemeasurable_sub_identity ha i j
    have hterm_meas : AEStronglyMeasurable
        (fun x => (a x - 1) i j * G x j) (volumeOn U) :=
      hcoeff.aestronglyMeasurable.mul hGj.aestronglyMeasurable
    have hentry :=
      ae_abs_matrix_sub_identity_entry_le_of_isMatrixPerturbationLE hclose
    have hbound : ∀ᵐ x ∂volumeOn U,
        ‖(a x - 1) i j * G x j‖ ≤ delta * ‖G x j‖ := by
      filter_upwards [hentry] with x hx
      calc
        ‖(a x - 1) i j * G x j‖ =
            |(a x - 1) i j| * ‖G x j‖ := by
              rw [norm_mul, Real.norm_eq_abs]
        _ ≤ delta * ‖G x j‖ :=
          mul_le_mul_of_nonneg_right (hx i j) (norm_nonneg _)
    exact MeasureTheory.MemLp.of_le_mul hGj hterm_meas hbound
  simpa only [matVecMul] using hsum

/-- A measurable coefficient field satisfying an almost everywhere operator
bound from the identity sends native-vector `L²(U)` fields through `a` into
native-vector `L²(U)`. The visible action bound has constant `1 + delta`. -/
theorem memVectorL2On_matVecMul_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {G : Vec d → Vec d}
    {delta : ℝ}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hG : MemVectorL2On U G) :
    MemVectorL2On U (fun x => matVecMul (a x) (G x)) := by
  classical
  intro i
  have hsum : MemLpOn U (2 : ℝ≥0∞)
      (fun x => ∑ j : Fin d, a x i j * G x j) := by
    refine MeasureTheory.memLp_finsetSum
      (s := Finset.univ)
      (f := fun j : Fin d => fun x : Vec d => a x i j * G x j) ?_
    intro j _hj
    have hGj : MemLpOn U (2 : ℝ≥0∞) (fun x => G x j) := hG j
    have hcoeff : AEMeasurable (fun x => a x i j) (volumeOn U) := by
      exact ha i j
    have hterm_meas : AEStronglyMeasurable
        (fun x => a x i j * G x j) (volumeOn U) :=
      hcoeff.aestronglyMeasurable.mul hGj.aestronglyMeasurable
    have hentry :=
      ae_abs_matrix_entry_le_one_add_delta_of_isMatrixPerturbationLE hclose
    have hbound : ∀ᵐ x ∂volumeOn U,
        ‖a x i j * G x j‖ ≤ (1 + delta) * ‖G x j‖ := by
      filter_upwards [hentry] with x hx
      calc
        ‖a x i j * G x j‖ = |a x i j| * ‖G x j‖ := by
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ (1 + delta) * ‖G x j‖ :=
          mul_le_mul_of_nonneg_right (hx i j) (norm_nonneg _)
    exact MeasureTheory.MemLp.of_le_mul hGj hterm_meas hbound
  simpa only [matVecMul] using hsum

end PDE
