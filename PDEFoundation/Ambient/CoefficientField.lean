module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Ambient.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Uniformly elliptic coefficient fields

This module supplies the native `Vec`/`Mat` coefficient convention, including
inverse coercivity, adjoints, and algebraic ellipticity transports.
-/

@[expose] public section

namespace PDE

/-- A matrix-valued coefficient field on the native coordinate space. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Nonsymmetric uniform ellipticity with the downstream inverse-coercivity convention. -/
def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

namespace IsEllipticMatrix

theorem lam_pos {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    0 < lam :=
  hA.1

theorem lam_le_Lam {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    lam ≤ Lam :=
  hA.2.1

theorem Lam_pos {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    0 < Lam :=
  lt_of_lt_of_le hA.lam_pos hA.lam_le_Lam

theorem coercive {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ) :=
  hA.2.2.1 ξ

theorem inverse_coercive {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ) :=
  hA.2.2.2 ξ

theorem mono {d : ℕ} {lam Lam lam' Lam' : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (hlam'_pos : 0 < lam') (hlam'_le : lam' ≤ lam)
    (hLam_le : Lam ≤ Lam') :
    IsEllipticMatrix lam' Lam' A := by
  refine ⟨hlam'_pos, hlam'_le.trans (hA.lam_le_Lam.trans hLam_le), ?_, ?_⟩
  · intro ξ
    calc
      lam' * vecNormSq ξ ≤ lam * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hlam'_le (vecNormSq_nonneg ξ)
      _ ≤ vecDot ξ (matVecMul A ξ) := hA.coercive ξ
  · intro ξ
    have hLam'_pos : 0 < Lam' := lt_of_lt_of_le hA.Lam_pos hLam_le
    have hInv_le : Lam'⁻¹ ≤ Lam⁻¹ := (inv_le_inv₀ hLam'_pos hA.Lam_pos).2 hLam_le
    calc
      Lam'⁻¹ * vecNormSq ξ ≤ Lam⁻¹ * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hInv_le (vecNormSq_nonneg ξ)
      _ ≤ vecDot ξ (matVecMul A⁻¹ ξ) := hA.inverse_coercive ξ

end IsEllipticMatrix

private theorem vecDot_matVecMul_transpose {d : ℕ} (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (matTranspose A) y) = vecDot (matVecMul A x) y := by
  calc
    vecDot x (matVecMul (matTranspose A) y)
        = ∑ i, ∑ j, x i * (A j i * y j) := by
          unfold vecDot matVecMul matTranspose
          congr with i
          rw [Finset.mul_sum]
          simp only [Matrix.transpose_apply]
    _ = ∑ j, ∑ i, (A j i * x i) * y j := by
          rw [Finset.sum_comm]
          congr with j
          congr with i
          ring
    _ = ∑ j, (∑ i, A j i * x i) * y j := by
          congr with j
          exact (Finset.sum_mul Finset.univ (fun i => A j i * x i) (y j)).symm
    _ = vecDot (matVecMul A x) y := by
          rfl

private theorem matVecMul_basisVec_apply {d : ℕ} (A : Mat d) (i j : Fin d) :
    matVecMul A (basisVec j) i = A i j := by
  unfold matVecMul basisVec
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, mul_one]
  · intro k _ hkj
    simp only [Pi.single_eq_of_ne hkj, mul_zero]
  · simp

private theorem vecDot_smul_right {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  calc
    vecDot x (c • y) = ∑ i, c * (x i * y i) := by
      simp only [vecDot, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = c * ∑ i, x i * y i := by
      symm
      exact Finset.mul_sum Finset.univ (fun i => x i * y i) c
    _ = c * vecDot x y := by rfl

theorem isUnit_det_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) : IsUnit A.det := by
  classical
  by_cases hdet : IsUnit A.det
  · exact hdet
  · have hInvZero : A⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit A hdet
    by_cases hd : d = 0
    · subst hd
      simp
    · let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
      have hbasis := hA.inverse_coercive (basisVec i)
      have hzero : vecDot (basisVec i) (matVecMul A⁻¹ (basisVec i)) = 0 := by
        rw [hInvZero]
        simp [matVecMul, vecDot]
      have hLamInv_nonpos : Lam⁻¹ ≤ 0 := by
        rw [vecNormSq_basisVec, hzero] at hbasis
        simpa using hbasis
      have hLamInv_pos : 0 < Lam⁻¹ := by
        exact inv_pos.mpr hA.Lam_pos
      linarith

/-- A nonzero scalar preserves matrix determinant invertibility. -/
theorem isUnit_det_smul {d : ℕ} {A : Mat d} (hdet : IsUnit A.det)
    {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • A).det := by
  rw [Matrix.det_smul]
  exact isUnit_iff_ne_zero.mpr <|
    mul_ne_zero (pow_ne_zero _ hc) (isUnit_iff_ne_zero.mp hdet)

/-- The nonsingular inverse of a nonzero scalar multiple. -/
theorem nonsing_inv_smul {d : ℕ} {A : Mat d} (c : ℝ) (hc : c ≠ 0)
    (hdet : IsUnit A.det) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  let : Invertible c := invertibleOfNonzero hc
  simpa using (Matrix.inv_smul (A := A) c hdet)

/-- Positive scalar rescaling transports ellipticity and both ellipticity constants. -/
theorem isEllipticMatrix_smul {d : ℕ} {lam Lam c : ℝ} {A : Mat d}
    (hc : 0 < c) (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix (c * lam) (c * Lam) (c • A) := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  refine ⟨mul_pos hc hA.lam_pos, mul_le_mul_of_nonneg_left hA.lam_le_Lam hc.le, ?_, ?_⟩
  · intro ξ
    have hmul := mul_le_mul_of_nonneg_left (hA.coercive ξ) hc.le
    change c * lam * vecNormSq ξ ≤ vecDot ξ (matVecMul (c • A) ξ)
    rw [show matVecMul (c • A) ξ = c • matVecMul A ξ by
      change (c • A).mulVec ξ = c • A.mulVec ξ
      exact Matrix.smul_mulVec c A ξ, vecDot_smul_right]
    nlinarith
  · intro ξ
    have hinv : (c • A)⁻¹ = c⁻¹ • A⁻¹ := nonsing_inv_smul c hc.ne' hdet
    have hmul := mul_le_mul_of_nonneg_left (hA.inverse_coercive ξ) (inv_pos.mpr hc).le
    have hconstants :
        (c * Lam)⁻¹ * vecNormSq ξ = c⁻¹ * (Lam⁻¹ * vecNormSq ξ) := by
      field_simp [hc.ne', hA.Lam_pos.ne']
    rw [hinv, show matVecMul (c⁻¹ • A⁻¹) ξ = c⁻¹ • matVecMul A⁻¹ ξ by
      change (c⁻¹ • A⁻¹).mulVec ξ = c⁻¹ • A⁻¹.mulVec ξ
      exact Matrix.smul_mulVec c⁻¹ A⁻¹ ξ, vecDot_smul_right, hconstants]
    exact hmul

/-- Inversion exchanges the ellipticity pair `(lam, Lam)` with `(Lam⁻¹, lam⁻¹)`. -/
theorem isEllipticMatrix_nonsingInv {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix Lam⁻¹ lam⁻¹ A⁻¹ := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  refine ⟨inv_pos.mpr hA.Lam_pos, ?_, hA.inverse_coercive, ?_⟩
  · exact (inv_le_inv₀ hA.Lam_pos hA.lam_pos).2 hA.lam_le_Lam
  · intro ξ
    simpa only [inv_inv, Matrix.nonsing_inv_nonsing_inv A hdet] using hA.coercive ξ

theorem vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul A ξ) ≤ Lam * vecDot ξ (matVecMul A ξ) := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  have hInvMul : matVecMul A⁻¹ (matVecMul A ξ) = ξ := by
    change A⁻¹.mulVec (A.mulVec ξ) = ξ
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec]
  have hInvA :
      Lam⁻¹ * vecNormSq (matVecMul A ξ) ≤ vecDot (matVecMul A ξ) ξ := by
    simpa only [hInvMul] using hA.inverse_coercive (matVecMul A ξ)
  have hscaled := mul_le_mul_of_nonneg_left hInvA hA.Lam_pos.le
  have hcancel : Lam * (Lam⁻¹ * vecNormSq (matVecMul A ξ)) = vecNormSq (matVecMul A ξ) := by
    field_simp [hA.Lam_pos.ne']
  rw [hcancel] at hscaled
  simpa only [vecDot_comm] using hscaled

theorem vecNormSq_matVecMul_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecNormSq (matVecMul A ξ) ≤ Lam ^ 2 * vecNormSq ξ := by
  have henergy := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA ξ
  have hcs : vecDot ξ (matVecMul A ξ) ^ 2 ≤
      vecNormSq ξ * vecNormSq (matVecMul A ξ) :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq ξ (matVecMul A ξ)
  have hdot_nonneg : 0 ≤ vecDot ξ (matVecMul A ξ) := by
    exact (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg ξ)).trans (hA.coercive ξ)
  by_cases hzero : vecNormSq (matVecMul A ξ) = 0
  · rw [hzero]
    exact mul_nonneg (sq_nonneg Lam) (vecNormSq_nonneg ξ)
  · have himage_pos : 0 < vecNormSq (matVecMul A ξ) :=
      lt_of_le_of_ne (vecNormSq_nonneg _) (by simpa only [eq_comm] using hzero)
    have hsquare : (vecNormSq (matVecMul A ξ)) ^ 2 ≤
        (Lam * vecDot ξ (matVecMul A ξ)) ^ 2 := by
      exact pow_le_pow_left₀ (vecNormSq_nonneg _) henergy 2
    have hmain : (vecNormSq (matVecMul A ξ)) ^ 2 ≤
        Lam ^ 2 * (vecNormSq ξ * vecNormSq (matVecMul A ξ)) := by
      calc
        (vecNormSq (matVecMul A ξ)) ^ 2 ≤
            (Lam * vecDot ξ (matVecMul A ξ)) ^ 2 := hsquare
        _ = Lam ^ 2 * vecDot ξ (matVecMul A ξ) ^ 2 := by ring
        _ ≤ Lam ^ 2 * (vecNormSq ξ * vecNormSq (matVecMul A ξ)) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg Lam)
    nlinarith

/-- The operator bound in the explicit Euclidean norm. -/
theorem vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    vecEuclideanNorm (matVecMul A ξ) ≤ Lam * vecEuclideanNorm ξ := by
  have hsq := vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ
  have hleft := vecEuclideanNorm_sq (matVecMul A ξ)
  have hright := vecEuclideanNorm_sq ξ
  have hright_nonneg : 0 ≤ Lam * vecEuclideanNorm ξ :=
    mul_nonneg hA.Lam_pos.le (vecEuclideanNorm_nonneg ξ)
  nlinarith

theorem abs_apply_le_of_isEllipticMatrix {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (i j : Fin d) :
    |A i j| ≤ Lam := by
  have hcoord_sq : (A i j) ^ 2 ≤ vecNormSq (matVecMul A (basisVec j)) := by
    rw [vecNormSq_eq_sum_sq]
    calc
      (A i j) ^ 2 = (matVecMul A (basisVec j) i) ^ 2 := by
        congr 1
        exact (matVecMul_basisVec_apply A i j).symm
      _ ≤ ∑ k, (matVecMul A (basisVec j) k) ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hupper : vecNormSq (matVecMul A (basisVec j)) ≤ Lam ^ 2 := by
    simpa only [vecNormSq_basisVec, mul_one] using
      vecNormSq_matVecMul_le_of_isEllipticMatrix hA (basisVec j)
  have habs_sq : |A i j| ^ 2 ≤ Lam ^ 2 := by
    simpa only [sq_abs] using hcoord_sq.trans hupper
  nlinarith [hA.Lam_pos.le, sq_nonneg (Lam - |A i j|)]

theorem isEllipticMatrix_transpose {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix lam Lam (matTranspose A) := by
  refine ⟨hA.lam_pos, hA.lam_le_Lam, ?_, ?_⟩
  · intro ξ
    calc
      lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ) := hA.coercive ξ
      _ = vecDot ξ (matVecMul (matTranspose A) ξ) := by
        rw [vecDot_matVecMul_transpose, vecDot_comm]
  · intro ξ
    have htransinv : matTranspose A⁻¹ = (matTranspose A)⁻¹ := by
      simpa only [matTranspose] using (Matrix.transpose_nonsing_inv (A := A))
    calc
      Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ) := hA.inverse_coercive ξ
      _ = vecDot ξ (matVecMul ((matTranspose A)⁻¹) ξ) := by
        rw [vecDot_comm, ← vecDot_matVecMul_transpose ξ ξ A⁻¹, htransinv]

/-- Measurable, uniformly elliptic coefficients on a domain, extended by zero outside it. -/
def IsEllipticFieldOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d)) (a : CoeffField d) : Prop :=
  by
    classical
    exact Measurable (fun x i j => if x ∈ U then a x i j else 0) ∧
      ∀ x ∈ U, IsEllipticMatrix lam Lam (a x)

/-- The transpose coefficient field. -/
abbrev transposeCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => matTranspose (a x)

/-- The adjoint coefficient field for real scalar divergence-form equations. -/
abbrev adjointCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  transposeCoeffField a

@[simp]
theorem transposeCoeffField_apply {d : ℕ} (a : CoeffField d) (x : Vec d) :
    transposeCoeffField a x = matTranspose (a x) :=
  rfl

@[simp]
theorem adjointCoeffField_apply {d : ℕ} (a : CoeffField d) (x : Vec d) :
    adjointCoeffField a x = matTranspose (a x) :=
  rfl

namespace IsEllipticFieldOn

theorem elliptic {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {x : Vec d} (hx : x ∈ U) :
    IsEllipticMatrix lam Lam (a x) :=
  hEll.2 x hx

theorem mono {d : ℕ} {lam Lam : ℝ} {U V : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (hV : MeasurableSet V) (hVU : V ⊆ U) :
    IsEllipticFieldOn lam Lam V a := by
  classical
  refine ⟨?_, fun x hx => hEll.elliptic (hVU hx)⟩
  refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
  have hmeasUij : Measurable (fun x : Vec d => if x ∈ U then a x i j else 0) := by
    simpa only using (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i) j)
  have hmeasVij : Measurable
      (V.piecewise (fun x : Vec d => if x ∈ U then a x i j else 0) (fun _ => 0)) :=
    hmeasUij.piecewise hV measurable_const
  convert hmeasVij using 1
  funext x
  by_cases hxV : x ∈ V
  · simp only [Set.piecewise, hxV, hVU hxV, ↓reduceIte]
  · simp only [Set.piecewise, hxV, ↓reduceIte]

theorem mono_constants {d : ℕ} {lam Lam lam' Lam' : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) (hlam'_pos : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    IsEllipticFieldOn lam' Lam' U a :=
  ⟨hEll.1, fun _ hx => (hEll.elliptic hx).mono hlam'_pos hlam'_le hLam_le⟩

theorem transpose {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam U (transposeCoeffField a) := by
  classical
  refine ⟨?_, fun x hx => isEllipticMatrix_transpose (hEll.elliptic hx)⟩
  refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
  have hji : Measurable (fun x : Vec d => if x ∈ U then a x j i else 0) :=
    measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 j) i
  exact hji

/-- Ellipticity is preserved by the real adjoint coefficient field. -/
theorem adjoint {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam U (adjointCoeffField a) :=
  hEll.transpose

end IsEllipticFieldOn

theorem abs_apply_le_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    |a x i j| ≤ Lam :=
  abs_apply_le_of_isEllipticMatrix (hEll.elliptic hx) i j

theorem measurableSet_of_isEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    MeasurableSet U := by
  classical
  by_cases hd : d = 0
  · subst hd
    exact Subsingleton.measurableSet
  · let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hdiag : Measurable (fun x => if x ∈ U then a x i i else 0) :=
      measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i) i
    have hU : U = {x | 0 < if x ∈ U then a x i i else 0} := by
      ext x
      constructor
      · intro hx
        have hdiag_lower : lam ≤ a x i i := by
          have hcoercive := (hEll.elliptic hx).coercive (basisVec i)
          rw [vecNormSq_basisVec, vecDot_basisVec_left, matVecMul_basisVec_apply] at hcoercive
          simpa only [mul_one] using hcoercive
        exact (show 0 < if x ∈ U then a x i i else 0 by
          simp only [hx, ↓reduceIte]
          exact lt_of_lt_of_le (hEll.elliptic hx).lam_pos hdiag_lower)
      · intro hx
        by_contra hxU
        change 0 < if x ∈ U then a x i i else 0 at hx
        have : (0 : ℝ) < 0 := by
          rw [ite_eq_right hxU] at hx
          exact hx
        linarith
    rw [hU]
    exact measurableSet_Ioi.preimage hdiag

noncomputable def restrictCoeffField {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :
    CoeffField d := by
  classical
  exact fun x => if x ∈ U then a x else 0

@[simp]
theorem restrictCoeffField_apply_of_mem {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {x : Vec d} (hx : x ∈ U) :
    restrictCoeffField U a x = a x := by
  simp only [restrictCoeffField, hx, ↓reduceIte]

@[simp]
theorem restrictCoeffField_apply_of_not_mem {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {x : Vec d} (hx : x ∉ U) :
    restrictCoeffField U a x = 0 := by
  simp only [restrictCoeffField, hx, ↓reduceIte]

end PDE
