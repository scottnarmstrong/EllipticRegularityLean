module

public import PDEFoundation.Ambient.EllipticNormalization
public import PDEFoundation.Ambient.CoefficientField

/-!
# Matrix facts for the time slice estimate

The quadratic form `qf A g h = g · (sym A) h` of the symmetric part of a coefficient matrix:
bilinearity, symmetry, non-negativity and the Young inequality for elliptic `A`; the pointwise
bounds `|A g · h|² ≤ (Λ/λ) (g·A g)(h·A h)` and `|A g|² ≤ Λ (g·A g)`.
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open PDE

variable {d : ℕ}

theorem vecDot_eq_dotProduct (x y : Vec d) : vecDot x y = x ⬝ᵥ y := rfl

theorem matVecMul_eq_mulVec (A : Mat d) (x : Vec d) : matVecMul A x = A.mulVec x := rfl

/-- The quadratic form of the symmetric part of `A`. -/
noncomputable def qf (A : Mat d) (g h : Vec d) : ℝ := vecDot g (matVecMul (symmPart A) h)

theorem qf_add_right (A : Mat d) (g h k : Vec d) : qf A g (h + k) = qf A g h + qf A g k := by
  simp only [qf, vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.mulVec_add, dotProduct_add]

theorem qf_add_left (A : Mat d) (g h k : Vec d) : qf A (g + h) k = qf A g k + qf A h k := by
  simp only [qf, vecDot_eq_dotProduct, matVecMul_eq_mulVec, add_dotProduct]

theorem qf_smul_right (A : Mat d) (g h : Vec d) (c : ℝ) : qf A g (c • h) = c * qf A g h := by
  simp only [qf, vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.mulVec_smul, dotProduct_smul,
    smul_eq_mul]

theorem qf_smul_left (A : Mat d) (g h : Vec d) (c : ℝ) : qf A (c • g) h = c * qf A g h := by
  simp only [qf, vecDot_eq_dotProduct, matVecMul_eq_mulVec, smul_dotProduct, smul_eq_mul]

theorem qf_sub_right (A : Mat d) (g h k : Vec d) : qf A g (h - k) = qf A g h - qf A g k := by
  simp only [qf, vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.mulVec_sub, dotProduct_sub]

theorem qf_sub_left (A : Mat d) (g h k : Vec d) : qf A (g - h) k = qf A g k - qf A h k := by
  simp only [qf, vecDot_eq_dotProduct, matVecMul_eq_mulVec, sub_dotProduct]

theorem qf_comm (A : Mat d) (g h : Vec d) : qf A g h = qf A h g := by
  simp only [qf, vecDot, matVecMul, symmPart, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qf_self (A : Mat d) (g : Vec d) : qf A g g = vecDot g (matVecMul A g) :=
  vecDot_symmPart_matVecMul A g

theorem qf_self_nonneg {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (g : Vec d) :
    0 ≤ qf A g g := by
  rw [qf_self]
  exact (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg g)).trans (hA.coercive g)

theorem lam_mul_vecNormSq_le_qf {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (g : Vec d) : lam * vecNormSq g ≤ qf A g g := by
  rw [qf_self]; exact hA.coercive g

theorem qf_self_le {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (g : Vec d) :
    vecNormSq (matVecMul A g) ≤ Lam * qf A g g := by
  rw [qf_self]; exact vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA g

/-- Young's inequality for the quadratic form: `2 q(g,h) ≤ ε⁻¹ q(g,g) + ε q(h,h)`. -/
theorem qf_young {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (g h : Vec d)
    {ε : ℝ} (hε : 0 < ε) : 2 * qf A g h ≤ ε⁻¹ * qf A g g + ε * qf A h h := by
  have h0 := qf_self_nonneg hA (g - ε • h)
  rw [qf_sub_left, qf_sub_right, qf_sub_right, qf_smul_right, qf_smul_left, qf_smul_left,
    qf_smul_right, qf_comm A h g] at h0
  have h1 : 0 ≤ ε⁻¹ * (qf A g g - ε * qf A g h - (ε * qf A g h - ε * (ε * qf A h h))) :=
    mul_nonneg (inv_nonneg.2 hε.le) (by linarith)
  have h2 : ε⁻¹ * (qf A g g - ε * qf A g h - (ε * qf A g h - ε * (ε * qf A h h))) =
      ε⁻¹ * qf A g g - 2 * qf A g h + ε * qf A h h := by
    field_simp
    ring
  linarith

/-- `|A g · h|² ≤ (Λ/λ) (g·A g)(h·A h)`. -/
theorem sq_vecDot_matVecMul_le {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (g h : Vec d) :
    vecDot (matVecMul A g) h ^ 2 ≤ (Lam / lam) * qf A g g * qf A h h := by
  have hT := isEllipticMatrix_transpose hA
  have h1 : vecDot (matVecMul A g) h = vecDot g (matVecMul (matTranspose A) h) := by
    rw [vecDot_eq_dotProduct, vecDot_eq_dotProduct, matVecMul_eq_mulVec, matVecMul_eq_mulVec,
      matTranspose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h2 : vecNormSq (matVecMul (matTranspose A) h) ≤ Lam * qf A h h := by
    have := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hT h
    have h3 : vecDot h (matVecMul (matTranspose A) h) = vecDot h (matVecMul A h) := by
      rw [vecDot_eq_dotProduct, vecDot_eq_dotProduct, matVecMul_eq_mulVec, matVecMul_eq_mulVec,
        matTranspose, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [h3] at this
    rwa [qf_self]
  have h4 : vecNormSq g ≤ lam⁻¹ * qf A g g := by
    have := lam_mul_vecNormSq_le_qf hA g
    rw [inv_mul_eq_div, le_div_iff₀ hA.lam_pos]
    linarith
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq g (matVecMul (matTranspose A) h)
  rw [h1]
  have hg0 := qf_self_nonneg hA g
  have hh0 := qf_self_nonneg hA h
  calc vecDot g (matVecMul (matTranspose A) h) ^ 2
      ≤ vecNormSq g * vecNormSq (matVecMul (matTranspose A) h) := hcs
    _ ≤ (lam⁻¹ * qf A g g) * (Lam * qf A h h) :=
        mul_le_mul h4 h2 (vecNormSq_nonneg _) (by have := hA.lam_pos; positivity)
    _ = (Lam / lam) * qf A g g * qf A h h := by field_simp

/-- `|A g · p|² ≤ Λ (g·A g) |p|²`. -/
theorem sq_vecDot_matVecMul_le_normSq {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (g p : Vec d) :
    vecDot (matVecMul A g) p ^ 2 ≤ Lam * qf A g g * vecNormSq p := by
  calc vecDot (matVecMul A g) p ^ 2 ≤ vecNormSq (matVecMul A g) * vecNormSq p :=
        sq_vecDot_le_vecNormSq_mul_vecNormSq _ _
    _ ≤ (Lam * qf A g g) * vecNormSq p :=
        mul_le_mul_of_nonneg_right (qf_self_le hA g) (vecNormSq_nonneg p)


/-- `g · A g ≤ Λ |g|²`. -/
theorem qf_le_Lam_normSq {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (g : Vec d) :
    qf A g g ≤ Lam * vecNormSq g := by
  have h0 := qf_self_nonneg hA g
  have hN := qf_self_le hA g
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq g (matVecMul A g)
  rw [← qf_self] at hcs
  have h1 : qf A g g ^ 2 ≤ vecNormSq g * (Lam * qf A g g) :=
    hcs.trans (mul_le_mul_of_nonneg_left hN (vecNormSq_nonneg g))
  by_contra hlt
  have hlt := not_le.mp hlt
  have hpos : 0 < qf A g g := lt_of_le_of_lt (mul_nonneg hA.Lam_pos.le (vecNormSq_nonneg g)) hlt
  have : qf A g g ≤ vecNormSq g * Lam := by
    have h2 : qf A g g * qf A g g ≤ (vecNormSq g * Lam) * qf A g g := by nlinarith [h1]
    exact le_of_mul_le_mul_right h2 hpos
  linarith

end PDE.Parabolic.Slice
