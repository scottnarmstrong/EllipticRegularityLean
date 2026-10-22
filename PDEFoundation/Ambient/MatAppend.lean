module

public import PDEFoundation.Ambient.Matrix
public import PDEFoundation.Ambient.VecAppend
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Block diagonal matrices on appended native coordinates

This file forms the literal block diagonal matrix associated to two native
matrices.  Its action and the explicit Euclidean dot product split exactly
across the two coordinate blocks.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- The block diagonal matrix with diagonal blocks `A` and `B`. -/
def matAppend {m n : ℕ} (A : Mat m) (B : Mat n) : Mat (m + n) :=
  Fin.addCases
    (fun i => Fin.addCases (fun j => A i j) (fun _ => 0))
    (fun i => Fin.addCases (fun _ => 0) (fun j => B i j))

@[simp]
theorem matAppend_apply_castAdd_castAdd {m n : ℕ} (A : Mat m) (B : Mat n)
    (i j : Fin m) :
    matAppend A B (Fin.castAdd n i) (Fin.castAdd n j) = A i j := by
  simp [matAppend]

@[simp]
theorem matAppend_apply_castAdd_natAdd {m n : ℕ} (A : Mat m) (B : Mat n)
    (i : Fin m) (j : Fin n) :
    matAppend A B (Fin.castAdd n i) (Fin.natAdd m j) = 0 := by
  simp [matAppend]

@[simp]
theorem matAppend_apply_natAdd_castAdd {m n : ℕ} (A : Mat m) (B : Mat n)
    (i : Fin n) (j : Fin m) :
    matAppend A B (Fin.natAdd m i) (Fin.castAdd n j) = 0 := by
  simp [matAppend]

@[simp]
theorem matAppend_apply_natAdd_natAdd {m n : ℕ} (A : Mat m) (B : Mat n)
    (i j : Fin n) :
    matAppend A B (Fin.natAdd m i) (Fin.natAdd m j) = B i j := by
  simp [matAppend]

/-- A block diagonal matrix acts separately on the two appended vectors. -/
theorem matAppend_mulVec_vecAppendEquiv_symm {m n : ℕ}
    (A : Mat m) (B : Mat n) (x : Vec m) (y : Vec n) :
    (matAppend A B).mulVec ((vecAppendEquiv m n).symm (x, y)) =
      (vecAppendEquiv m n).symm (A.mulVec x, B.mulVec y) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/-- The explicit Euclidean dot product is additive across appended vectors. -/
theorem vecDot_vecAppendEquiv_symm {m n : ℕ}
    (x x' : Vec m) (y y' : Vec n) :
    vecDot ((vecAppendEquiv m n).symm (x, y))
        ((vecAppendEquiv m n).symm (x', y')) =
      vecDot x x' + vecDot y y' := by
  unfold vecDot
  rw [Fin.sum_univ_add]
  simp only [vecAppendEquiv_symm_apply_castAdd,
    vecAppendEquiv_symm_apply_natAdd]

end PDE
