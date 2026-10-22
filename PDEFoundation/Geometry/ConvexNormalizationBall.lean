module

public import PDEFoundation.Geometry.ConvexNormalizationSimplex
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Containment steps for the affine normalization of a convex domain

With `M = simplexMat v` the matrix of a maximal simplex, points of `V` have
barycentric coordinates in `(-1, 1)`, and the Euclidean ball of radius
`r = (d + √d)⁻¹` about `r • 1` in barycentric coordinates lies in `V`.
-/

@[expose] public section

open Set

namespace PDE

section

variable {d : ℕ} {V : Set (Vec d)} {v : Fin (d + 1) → Vec d}

theorem simplexMat_mulVec_inv_mulVec (hM : (simplexMat v).det ≠ 0) (b : Vec d) :
    (simplexMat v).mulVec ((simplexMat v)⁻¹.mulVec b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM.isUnit, Matrix.one_mulVec]

theorem simplexMat_inv_mulVec_mulVec (hM : (simplexMat v).det ≠ 0) (y : Vec d) :
    (simplexMat v)⁻¹.mulVec ((simplexMat v).mulVec y) = y := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM.isUnit, Matrix.one_mulVec]

/-- Points of the open set have barycentric coordinates strictly inside `(-1, 1)`. -/
theorem abs_coord_lt_one_of_mem (hV : IsOpen V)
    (hmax : ∀ x ∈ closure V, ∀ y : Vec d, (simplexMat v).mulVec y = x - v 0 →
        ∀ i, |y i| ≤ 1)
    {x : Vec d} (hx : x ∈ V) {y : Vec d}
    (hy : (simplexMat v).mulVec y = x - v 0) (i : Fin d) : |y i| < 1 := by
  have hcont : Continuous fun t : ℝ => x + t • (x - v 0) := by fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), x + t • (x - v 0) ∈ V := by
    have := hcont.tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.eventually (hV.mem_nhds hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ε : ℝ := δ / 2 with hε
  have hεpos : 0 < ε := half_pos hδ
  have hmem : x + ε • (x - v 0) ∈ V :=
    hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]; linarith)
  have hy' : (simplexMat v).mulVec ((1 + ε) • y) = (x + ε • (x - v 0)) - v 0 := by
    rw [Matrix.mulVec_smul, hy, add_smul, one_smul]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have h1 := hmax _ (subset_closure hmem) _ hy' i
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 + ε)] at h1
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Points with nonnegative coordinates of sum at most one lie in the simplex. -/
theorem simplex_point_mem_closure (hvK : ∀ i, v i ∈ closure V)
    (hconv : Convex ℝ (closure V)) {y : Vec d} (hy0 : ∀ i, 0 ≤ y i)
    (hy1 : ∑ i, y i ≤ 1) :
    v 0 + (simplexMat v).mulVec y ∈ closure V := by
  let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, y i) y
  have hsum : ∑ k, w k = 1 := by
    simp [w, Fin.sum_univ_succ]
  have hpt : v 0 + (simplexMat v).mulVec y = ∑ k, w k • v k := by
    ext j
    simp only [simplexMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    have : ∑ x, y x * v x.succ j = ∑ x, v x.succ j * y x :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [this]
    ring
  rw [hpt]
  refine hconv.sum_mem (fun k _ => ?_) hsum (fun k _ => hvK k)
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa [w] using hy1
  · simpa [w] using hy0 i

theorem sum_le_sqrt_mul_vecEuclideanNorm (w : Vec d) :
    ∑ i, w i ≤ Real.sqrt d * vecEuclideanNorm w := by
  have h1 : vecEuclideanNorm (1 : Vec d) = Real.sqrt d := by
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  have := (le_abs_self (vecDot w 1)).trans (abs_vecDot_le_vecEuclideanNorm_mul w 1)
  simpa [vecDot, h1, mul_comm] using this

/-- The Euclidean ball of radius `r = (d + √d)⁻¹` about `r • 1`, in barycentric
coordinates, lies in `V`. -/
theorem mem_of_barycentric_ball (hd : 1 ≤ d) (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty)
    (hvK : ∀ i, v i ∈ closure V) (hM : (simplexMat v).det ≠ 0) {x : Vec d}
    (hx : vecEuclideanNorm ((simplexMat v)⁻¹.mulVec (x - v 0) -
      (Real.sqrt d + d : ℝ)⁻¹ • (1 : Vec d)) < (Real.sqrt d + d : ℝ)⁻¹) :
    x ∈ V := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set r : ℝ := (Real.sqrt d + d : ℝ)⁻¹ with hr
  have hrr : r * (Real.sqrt d + d) = 1 := inv_mul_cancel₀ (by positivity)
  have hconv : Convex ℝ (closure V) := hV.convex.closure
  have hint : interior (closure V) = V := by
    rw [hV.convex.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hV.isOpen.interior_eq]; exact hne), hV.isOpen.interior_eq]
  let S : Set (Vec d) := {x | vecEuclideanNorm ((simplexMat v)⁻¹.mulVec (x - v 0) -
      r • (1 : Vec d)) < r}
  have hSopen : IsOpen S := by
    refine isOpen_lt ?_ continuous_const
    refine continuous_vecEuclideanNorm.comp ?_
    have : Continuous fun x : Vec d => (simplexMat v)⁻¹.mulVec (x - v 0) :=
      (Matrix.mulVecLin (simplexMat v)⁻¹).continuous_of_finiteDimensional.comp
        (continuous_id.sub continuous_const)
    exact this.sub continuous_const
  have hSK : S ⊆ closure V := by
    intro x hxS
    set y := (simplexMat v)⁻¹.mulVec (x - v 0) with hy
    have hxy : x = v 0 + (simplexMat v).mulVec y := by
      rw [hy, simplexMat_mulVec_inv_mulVec hM]; abel
    have hcoord : ∀ i, |y i - r| < r := fun i =>
      lt_of_le_of_lt (by simpa using abs_apply_le_vecEuclideanNorm (y - r • (1 : Vec d)) i) hxS
    have hy0 : ∀ i, 0 ≤ y i := fun i => by
      have := (abs_lt.1 (hcoord i)).1; linarith
    have hsum := sum_le_sqrt_mul_vecEuclideanNorm (y - r • (1 : Vec d))
    have hsum' : ∑ i, y i ≤ 1 := by
      have hc : ∑ i : Fin d, r * (1 : Vec d) i = d * r := by
        simp [mul_comm]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, hc] at hsum
      have : Real.sqrt d * vecEuclideanNorm (y - r • (1 : Vec d)) ≤ Real.sqrt d * r :=
        mul_le_mul_of_nonneg_left hxS.le hsd.le
      nlinarith
    rw [hxy]
    exact simplex_point_mem_closure hvK hconv hy0 hsum'
  have := interior_maximal hSK hSopen
  rw [hint] at this
  exact this hx

end

end PDE
