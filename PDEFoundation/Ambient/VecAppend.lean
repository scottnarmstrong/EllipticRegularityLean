module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Splitting native coordinate vectors

This file identifies a vector indexed by `Fin (m + n)` with its first `m`
coordinates and remaining `n` coordinates.  The equivalence is literal
coordinate splitting, and the explicit Euclidean squared norm is additive
across the split.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- Split a native vector into its first `m` and remaining `n` coordinates. -/
def vecAppendEquiv (m n : ℕ) : Vec (m + n) ≃L[ℝ] (Vec m × Vec n) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (m + n) => ℝ)
      finSumFinEquiv).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin m) (Fin n) (fun _ => ℝ))

@[simp]
theorem vecAppendEquiv_apply_fst (m n : ℕ) (x : Vec (m + n)) (i : Fin m) :
    (vecAppendEquiv m n x).1 i = x (Fin.castAdd n i) := rfl

@[simp]
theorem vecAppendEquiv_apply_snd (m n : ℕ) (x : Vec (m + n)) (j : Fin n) :
    (vecAppendEquiv m n x).2 j = x (Fin.natAdd m j) := rfl

@[simp]
theorem vecAppendEquiv_symm_apply_castAdd (m n : ℕ) (x : Vec m × Vec n)
    (i : Fin m) :
    (vecAppendEquiv m n).symm x (Fin.castAdd n i) = x.1 i := by
  have h := congrFun (congrArg Prod.fst
    ((vecAppendEquiv m n).apply_symm_apply x)) i
  simpa only [vecAppendEquiv_apply_fst] using h

@[simp]
theorem vecAppendEquiv_symm_apply_natAdd (m n : ℕ) (x : Vec m × Vec n)
    (j : Fin n) :
    (vecAppendEquiv m n).symm x (Fin.natAdd m j) = x.2 j := by
  have h := congrFun (congrArg Prod.snd
    ((vecAppendEquiv m n).apply_symm_apply x)) j
  simpa only [vecAppendEquiv_apply_snd] using h

/-- The Euclidean squared norm is additive under the coordinate split. -/
theorem vecNormSq_vecAppendEquiv_symm (m n : ℕ) (x : Vec m × Vec n) :
    vecNormSq ((vecAppendEquiv m n).symm x) = vecNormSq x.1 + vecNormSq x.2 := by
  simp only [vecNormSq_eq_sum_sq]
  rw [Fin.sum_univ_add]
  simp only [vecAppendEquiv_symm_apply_castAdd, vecAppendEquiv_symm_apply_natAdd]

/-- The Euclidean squared norm is additive under the coordinate split. -/
theorem vecNormSq_vecAppendEquiv (m n : ℕ) (x : Vec (m + n)) :
    vecNormSq x = vecNormSq (vecAppendEquiv m n x).1 +
      vecNormSq (vecAppendEquiv m n x).2 := by
  rw [← vecNormSq_vecAppendEquiv_symm m n (vecAppendEquiv m n x)]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

end PDE
