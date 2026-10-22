module

public import PDEFoundation.Ambient.VecAppend
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-! # Round balls under native coordinate splitting -/

@[expose] public section

namespace PDE

open Set

/-- A round ball lies in the product of the same-radius round balls after
splitting its coordinates. -/
theorem euclideanBall_subset_preimage_vecAppendEquiv_prod
    (m n : ℕ) {R : ℝ} (hR : 0 < R) :
    euclideanBall (0 : Vec (m + n)) R ⊆
      vecAppendEquiv m n ⁻¹'
        (euclideanBall (0 : Vec m) R ×ˢ euclideanBall (0 : Vec n) R) := by
  intro x hx
  have hxNorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx
  simp only [sub_zero] at hxNorm
  have hsq := vecNormSq_vecAppendEquiv m n x
  have hfstSq : vecNormSq (vecAppendEquiv m n x).1 ≤ vecNormSq x := by
    rw [hsq]
    exact le_add_of_nonneg_right (vecNormSq_nonneg _)
  have hsndSq : vecNormSq (vecAppendEquiv m n x).2 ≤ vecNormSq x := by
    rw [hsq]
    exact le_add_of_nonneg_left (vecNormSq_nonneg _)
  have hfstNorm : vecEuclideanNorm (vecAppendEquiv m n x).1 ≤
      vecEuclideanNorm x := by
    exact Real.sqrt_le_sqrt hfstSq
  have hsndNorm : vecEuclideanNorm (vecAppendEquiv m n x).2 ≤
      vecEuclideanNorm x := by
    exact Real.sqrt_le_sqrt hsndSq
  constructor
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
    simpa only [sub_zero] using hfstNorm.trans_lt hxNorm
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
    simpa only [sub_zero] using hsndNorm.trans_lt hxNorm

/-- The inverse image of the product of the two half-radius round balls lies
in the full round ball. -/
theorem preimage_vecAppendEquiv_prod_halfBall_subset_euclideanBall
    (m n : ℕ) {R : ℝ} (hR : 0 < R) :
    vecAppendEquiv m n ⁻¹'
        (euclideanBall (0 : Vec m) (R / 2) ×ˢ
          euclideanBall (0 : Vec n) (R / 2)) ⊆
      euclideanBall (0 : Vec (m + n)) R := by
  intro x hx
  have hhalf : 0 < R / 2 := half_pos hR
  have hfst := (mem_euclideanBall_iff_vecEuclideanNorm_lt hhalf).1 hx.1
  have hsnd := (mem_euclideanBall_iff_vecEuclideanNorm_lt hhalf).1 hx.2
  simp only [sub_zero] at hfst hsnd
  have hfstSq := vecEuclideanNorm_sq (vecAppendEquiv m n x).1
  have hsndSq := vecEuclideanNorm_sq (vecAppendEquiv m n x).2
  have hxSq := vecEuclideanNorm_sq x
  have hsplit := vecNormSq_vecAppendEquiv m n x
  have hfstNonneg := vecEuclideanNorm_nonneg (vecAppendEquiv m n x).1
  have hsndNonneg := vecEuclideanNorm_nonneg (vecAppendEquiv m n x).2
  have hxNonneg := vecEuclideanNorm_nonneg x
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
  simp only [sub_zero]
  nlinarith [sq_nonneg (R / 2), sq_nonneg R]

end PDE
