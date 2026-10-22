module

public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Maximal-volume simplex in the closure of a convex domain

For a nonempty bounded open set `V`, the function
`(x₀, …, x_d) ↦ |det (x₁ - x₀, …, x_d - x₀)|` attains its maximum on
`(closure V)^(d+1)`, the maximum is positive, and the barycentric coordinates
of every point of `closure V` with respect to a maximizing simplex are bounded
by one in absolute value (Cramer's rule).
-/

@[expose] public section

open Set

namespace PDE

/-- The matrix whose columns are `v (i+1) - v 0`. -/
def simplexMat {d : ℕ} (v : Fin (d + 1) → Vec d) : Mat d :=
  Matrix.of fun j i => v i.succ j - v 0 j

theorem continuous_simplexMat_det {d : ℕ} :
    Continuous fun v : Fin (d + 1) → Vec d => (simplexMat v).det := by
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun j i => ?_
  simp only [simplexMat, Matrix.of_apply]
  fun_prop

/-- A small coordinate simplex inside an open set has nonzero determinant. -/
theorem exists_simplex_mem_det_ne_zero {d : ℕ} {V : Set (Vec d)}
    (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ v : Fin (d + 1) → Vec d, (∀ i, v i ∈ V) ∧ (simplexMat v).det ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x₀ hx₀
  refine ⟨Fin.cons x₀ fun i => x₀ + (ε / 2) • Pi.single i 1, ?_, ?_⟩
  · intro i
    refine Fin.cases hx₀ (fun k => hball ?_) i
    rw [Fin.cons_succ, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    have : ‖(Pi.single k 1 : Vec d)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      by_cases h : j = k
      · subst h; simp
      · simp [h]
    nlinarith [half_pos hε, norm_nonneg (Pi.single k 1 : Vec d)]
  · have hmat : simplexMat (Fin.cons x₀ fun i => x₀ + (ε / 2) • Pi.single i 1 :
        Fin (d + 1) → Vec d) = (ε / 2) • (1 : Mat d) := by
      ext j i
      simp only [simplexMat, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero,
        Pi.add_apply, Pi.smul_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, add_sub_cancel_left]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (half_pos hε).ne'

theorem det_updateCol_simplexMat {d : ℕ} (v : Fin (d + 1) → Vec d)
    (i : Fin d) (x : Vec d) :
    (Matrix.updateCol (simplexMat v) i (x - v 0)).det =
      (simplexMat (Function.update v i.succ x)).det := by
  congr 1
  ext j k
  by_cases h : k = i
  · subst h
    simp [simplexMat, Function.update_of_ne (Fin.succ_ne_zero k).symm]
  · have : k.succ ≠ i.succ := fun h' => h (Fin.succ_injective _ h')
    have h0 : (0 : Fin (d + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp [simplexMat, Function.update_of_ne h0, h]

/-- Cramer's rule: the coordinates of `y` with `M y = x - v₀`. -/
theorem det_simplexMat_mul_coord {d : ℕ} (v : Fin (d + 1) → Vec d)
    (x : Vec d) (y : Vec d)
    (hy : (simplexMat v).mulVec y = x - v 0) (i : Fin d) :
    (simplexMat (Function.update v i.succ x)).det =
      (simplexMat v).det * y i := by
  rw [← det_updateCol_simplexMat, ← Matrix.cramer_apply, ← hy,
    Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul]
  simp [Matrix.smul_mulVec]

/-- A maximal-volume simplex in the closure of a nonempty bounded open set:
its vertices lie in the closure, its determinant is nonzero, and the
barycentric coordinates of every point of the closure are bounded by one. -/
theorem exists_maxSimplex {d : ℕ} {V : Set (Vec d)}
    (hV : IsOpen V) (hb : IsBoundedDomain V) (hne : V.Nonempty) :
    ∃ v : Fin (d + 1) → Vec d, (∀ i, v i ∈ closure V) ∧
      (simplexMat v).det ≠ 0 ∧
      ∀ x ∈ closure V, ∀ y : Vec d, (simplexMat v).mulVec y = x - v 0 →
        ∀ i, |y i| ≤ 1 := by
  have hK : IsCompact (closure V) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.isBounded.closure
  have hP : IsCompact (Set.pi Set.univ fun _ : Fin (d + 1) => closure V) :=
    isCompact_univ_pi fun _ => hK
  obtain ⟨w, hwV, hwdet⟩ := exists_simplex_mem_det_ne_zero hV hne
  have hPne : (Set.pi Set.univ fun _ : Fin (d + 1) => closure V).Nonempty :=
    ⟨w, fun i _ => subset_closure (hwV i)⟩
  obtain ⟨v, hvP, hvmax⟩ := hP.exists_isMaxOn hPne
    (continuous_simplexMat_det (d := d)).abs.continuousOn
  have hvK : ∀ i, v i ∈ closure V := fun i => hvP i (mem_univ i)
  have hwP : w ∈ Set.pi Set.univ fun _ : Fin (d + 1) => closure V :=
    fun i _ => subset_closure (hwV i)
  have hle : |(simplexMat w).det| ≤ |(simplexMat v).det| := hvmax hwP
  have hpos : 0 < |(simplexMat v).det| :=
    lt_of_lt_of_le (abs_pos.2 hwdet) hle
  refine ⟨v, hvK, abs_pos.1 hpos, ?_⟩
  intro x hx y hy i
  have hmem : Function.update v i.succ x ∈
      Set.pi Set.univ fun _ : Fin (d + 1) => closure V := by
    intro k _
    by_cases h : k = i.succ
    · subst h; simpa using hx
    · simpa [Function.update_of_ne h] using hvK k
  have h1 := hvmax hmem
  simp only [mem_ofPred_eq] at h1
  rw [det_simplexMat_mul_coord v x y hy i, abs_mul] at h1
  exact (mul_le_iff_le_one_right hpos).1 h1

end PDE
