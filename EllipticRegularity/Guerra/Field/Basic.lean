module

public import PDEFoundation

/-!
# Guerra sharpness: the ambient matrix field, radius/latitude algebra

Definitions and elementary algebra for the matrix field
`B(x) = 1 + (b-1) ω⊗ω + ω⊗Y`, `Y = h(t) q`, of the proof of Proposition 4.30.  The
distinguished coordinate `e_d` of the manuscript is an arbitrary index `j : Fin d`; the
scalar profile `h` is a parameter, so nothing here depends on the scalar toolbox.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- `b = 400 γ²`. -/
def bcoef (γ : ℝ) : ℝ := 400 * γ ^ 2

/-- The radius `r = |x|` (Euclidean). -/
def rad (x : Vec d) : ℝ := vecEuclideanNorm x

/-- The unit direction `ω = x / r` (equal to `0` at the origin). -/
def omega (x : Vec d) : Vec d := (rad x)⁻¹ • x

/-- The latitude `t = x_j / r`. -/
def lat (j : Fin d) (x : Vec d) : ℝ := x j / rad x

/-- The tangential vector `q = e_j - t ω`. -/
def qvec (j : Fin d) (x : Vec d) : Vec d := basisVec j - lat j x • omega x

/-- `Y = h(t) q`. -/
def yvec (h : ℝ → ℝ) (j : Fin d) (x : Vec d) : Vec d := h (lat j x) • qvec j x

/-- The matrix field `B(x) = 1 + (b-1) ω⊗ω + ω⊗Y` with `b = 400γ²`; `B(0) = 1`
because `ω(0) = 0`. -/
def fieldMatrix (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) : Mat d :=
  (1 : Mat d) + (bcoef γ - 1) • Matrix.vecMulVec (omega x) (omega x) +
    Matrix.vecMulVec (omega x) (yvec h j x)

/-! ### Radius and latitude algebra -/

theorem rad_pos {x : Vec d} (hx : x ≠ 0) : 0 < rad x :=
  vecEuclideanNorm_pos_iff.mpr hx

theorem rad_zero : rad (0 : Vec d) = 0 :=
  vecEuclideanNorm_eq_zero_iff.mpr rfl

theorem rad_sq (x : Vec d) : rad x ^ 2 = vecNormSq x := vecEuclideanNorm_sq x

theorem omega_zero : omega (0 : Vec d) = 0 := by simp [omega]

theorem vecDot_smul_left (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_smul_right (c : ℝ) (x y : Vec d) : vecDot x (c • y) = c * vecDot x y := by
  rw [vecDot_comm, vecDot_smul_left, vecDot_comm]

theorem vecDot_sub_left (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem vecDot_sub_right (x y z : Vec d) : vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [vecDot_comm, vecDot_sub_left, vecDot_comm, vecDot_comm z]

theorem vecDot_add_left (x y z : Vec d) : vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem vecDot_add_right (x y z : Vec d) : vecDot x (y + z) = vecDot x y + vecDot x z := by
  rw [vecDot_comm, vecDot_add_left, vecDot_comm, vecDot_comm z]

theorem vecDot_self_eq (x : Vec d) : vecDot x x = vecNormSq x := rfl

/-- `x = r ω` for `x ≠ 0`. -/
theorem smul_omega {x : Vec d} (hx : x ≠ 0) : rad x • omega x = x := by
  have := (rad_pos hx).ne'
  simp [omega, smul_smul, this]

theorem vecNormSq_omega {x : Vec d} (hx : x ≠ 0) : vecDot (omega x) (omega x) = 1 := by
  have hr := (rad_pos hx).ne'
  rw [omega, vecDot_smul_left, vecDot_smul_right, vecDot_self_eq, ← rad_sq]
  field_simp

theorem vecDot_omega_basisVec {x : Vec d} (j : Fin d) :
    vecDot (omega x) (basisVec j) = lat j x := by
  rw [vecDot_basisVec_right]
  simp [omega, lat, div_eq_inv_mul]

theorem vecDot_omega_qvec {x : Vec d} (hx : x ≠ 0) (j : Fin d) :
    vecDot (omega x) (qvec j x) = 0 := by
  rw [qvec, vecDot_sub_right, vecDot_smul_right, vecNormSq_omega hx, vecDot_omega_basisVec]
  ring

theorem vecDot_qvec_qvec {x : Vec d} (hx : x ≠ 0) (j : Fin d) :
    vecDot (qvec j x) (qvec j x) = 1 - lat j x ^ 2 := by
  have h1 : vecDot (qvec j x) (omega x) = 0 := by
    rw [vecDot_comm]; exact vecDot_omega_qvec hx j
  have h2 : vecDot (basisVec j) (omega x) = lat j x := by
    rw [vecDot_comm]; exact vecDot_omega_basisVec j
  have h3 : vecDot (basisVec j) (basisVec j) = 1 := by
    rw [vecDot_basisVec_right]; simp
  conv_lhs => rw [qvec]
  rw [vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_smul_left, vecDot_smul_left,
    vecDot_smul_right, vecDot_smul_right, vecNormSq_omega hx, h2, h3,
    vecDot_comm (omega x) (basisVec j), h2]
  ring

theorem lat_sq_le_one (j : Fin d) (x : Vec d) : lat j x ^ 2 ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp [lat, rad_zero]
  · have hr := rad_pos hx
    have h := abs_apply_le_vecEuclideanNorm x j
    have : |x j / rad x| ≤ 1 := by
      rw [abs_div, abs_of_pos hr, div_le_one hr]; exact h
    have := sq_le_one_iff_abs_le_one _ |>.mpr this
    simpa [lat] using this

theorem abs_lat_le_one (j : Fin d) (x : Vec d) : |lat j x| ≤ 1 :=
  (sq_le_one_iff_abs_le_one _).mp (lat_sq_le_one j x)

theorem vecDot_yvec_yvec {x : Vec d} (hx : x ≠ 0) (h : ℝ → ℝ) (j : Fin d) :
    vecDot (yvec h j x) (yvec h j x) = h (lat j x) ^ 2 * (1 - lat j x ^ 2) := by
  rw [yvec, vecDot_smul_left, vecDot_smul_right, vecDot_qvec_qvec hx]; ring

theorem vecDot_omega_yvec {x : Vec d} (hx : x ≠ 0) (h : ℝ → ℝ) (j : Fin d) :
    vecDot (omega x) (yvec h j x) = 0 := by
  rw [yvec, vecDot_smul_right, vecDot_omega_qvec hx]; ring

theorem vecDot_yvec_omega {x : Vec d} (hx : x ≠ 0) (h : ℝ → ℝ) (j : Fin d) :
    vecDot (yvec h j x) (omega x) = 0 := by
  rw [vecDot_comm]; exact vecDot_omega_yvec hx h j

/-- `|Y|² ≤ b/4` when `|h| ≤ 10γ`. -/
theorem vecDot_yvec_yvec_le {x : Vec d} (hx : x ≠ 0) {γ : ℝ} (h : ℝ → ℝ) (j : Fin d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) :
    vecDot (yvec h j x) (yvec h j x) ≤ bcoef γ / 4 := by
  rw [vecDot_yvec_yvec hx]
  have h1 := hh _ (abs_lat_le_one j x)
  have h2 := lat_sq_le_one j x
  have h3 : h (lat j x) ^ 2 ≤ (10 * γ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (h (lat j x))) h1 2
    rwa [sq_abs] at this
  have h4 : 0 ≤ 1 - lat j x ^ 2 := by linarith
  unfold bcoef
  nlinarith [sq_nonneg (lat j x)]

end

end PDE.Guerra
