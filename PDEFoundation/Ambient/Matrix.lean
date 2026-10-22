module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Tactic.Ring

/-!
# Matrices on native vectors

Coordinate definitions of matrix action, transpose, and symmetric and
skew-symmetric parts, shared by the weak PDE and homogenization layers.
-/

@[expose] public section

namespace PDE

/-- Coordinate matrix-vector multiplication on `Mat d` and `Vec d`. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

/-- Matrix transpose, named independently of notation for compatibility. -/
def matTranspose {d : ℕ} (A : Mat d) : Mat d :=
  Matrix.transpose A

@[simp]
theorem matVecMul_apply {d : ℕ} (A : Mat d) (x : Vec d) (i : Fin d) :
    matVecMul A x i = ∑ j, A i j * x j :=
  rfl

@[simp]
theorem matTranspose_apply {d : ℕ} (A : Mat d) (i j : Fin d) :
    matTranspose A i j = A j i :=
  rfl

/-- The symmetric part `(A + Aᵀ) / 2`. -/
noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

/-- The skew-symmetric part `(A - Aᵀ) / 2`. -/
noncomputable def skewPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j - A j i) / 2

theorem symmPart_eq_smul_add_transpose {d : ℕ} (A : Mat d) :
    symmPart A = (1 / 2 : ℝ) • (A + matTranspose A) := by
  ext i j
  simp [symmPart, matTranspose]
  ring

theorem skewPart_eq_smul_sub_transpose {d : ℕ} (A : Mat d) :
    skewPart A = (1 / 2 : ℝ) • (A - matTranspose A) := by
  ext i j
  simp [skewPart, matTranspose]
  ring

@[simp]
theorem matTranspose_symmPart {d : ℕ} (A : Mat d) :
    matTranspose (symmPart A) = symmPart A := by
  ext i j
  simp [matTranspose, symmPart]
  ring

@[simp]
theorem matTranspose_skewPart {d : ℕ} (A : Mat d) :
    matTranspose (skewPart A) = -skewPart A := by
  ext i j
  simp [matTranspose, skewPart]
  ring

end PDE
