module

public import PDEFoundation

/-!
# Algebra for the Guerra symmetrization

Vector and matrix identities and the explicit symmetrization formula of
Lemma 4.31.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.GuerraSymmetrizeProof

variable {d : ℕ}

lemma vecDot_add_right (x y z : Vec d) : vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

lemma vecDot_sub_right (x y z : Vec d) : vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

lemma vecDot_smul_right (x y : Vec d) (c : ℝ) : vecDot x (c • y) = c * vecDot x y := by
  simp [vecDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma vecDot_add_left (x y z : Vec d) : vecDot (x + y) z = vecDot x z + vecDot y z := by
  rw [vecDot_comm, vecDot_add_right, vecDot_comm z x, vecDot_comm z y]

lemma vecDot_sub_left (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [vecDot_comm, vecDot_sub_right, vecDot_comm z x, vecDot_comm z y]

lemma vecDot_smul_left (x y : Vec d) (c : ℝ) : vecDot (c • x) y = c * vecDot x y := by
  rw [vecDot_comm, vecDot_smul_right, vecDot_comm]

lemma matVecMul_eq_mulVec (A : Mat d) (x : Vec d) : matVecMul A x = A.mulVec x := rfl

/-- The explicit symmetrized matrix. -/
noncomputable def form (σ : ℝ) (e z : Vec d) : Mat d :=
  Matrix.of fun i j => (if i = j then σ else 0) + e i * z j + z i * e j + 2 / σ * (z i * z j)

lemma form_apply (σ : ℝ) (e z : Vec d) (ξ : Vec d) :
    matVecMul (form σ e z) ξ =
      σ • ξ + vecDot z ξ • e + vecDot e ξ • z + (2 / σ * vecDot z ξ) • z := by
  funext i
  simp only [matVecMul, form, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    vecDot, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ (f : Fin d → ℝ), ∑ j, e i * z j * ξ j = ∑ j, e i * (z j * ξ j) := fun f => by
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, z i * e j * ξ j = ∑ j, z i * (e j * ξ j) :=
    Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ j, 2 / σ * (z i * z j) * ξ j = ∑ j, 2 / σ * z i * (z j * ξ j) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [h1 0, h2, h3]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma form_symm (σ : ℝ) (e z : Vec d) (i j : Fin d) : form σ e z i j = form σ e z j i := by
  simp only [form, Matrix.of_apply]
  have : (if i = j then σ else 0) = (if j = i then σ else 0) := by
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [this]
  ring

lemma vecDot_form (σ : ℝ) (e z ξ : Vec d) :
    vecDot ξ (matVecMul (form σ e z) ξ) =
      σ * vecNormSq ξ + 2 * (vecDot ξ e * vecDot ξ z) + 2 / σ * vecDot ξ z ^ 2 := by
  rw [form_apply]
  simp only [vecDot_add_right, vecDot_smul_right]
  rw [vecDot_comm z ξ, vecDot_comm e ξ]
  unfold vecNormSq
  ring

end PDE.GuerraSymmetrizeProof
