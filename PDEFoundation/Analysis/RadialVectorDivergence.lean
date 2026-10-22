module

public import PDEFoundation.Analysis.RadialQuadraticDerivative

/-!
# Divergence of two-term radial vector fields
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- A coordinate radial vector field with one axial and one radial term. -/
noncomputable def radialVectorField {d : ℕ}
    (a b s : ℝ) (k : Fin d) (x : Vec d) : Vec d :=
  (a * (vecNormSq x) ^ s) • basisVec k +
    (b * x k * (vecNormSq x) ^ (s - 1)) • x

private theorem differentiableAt_vecNormSq_vector {d : ℕ} (x : Vec d) :
    DifferentiableAt ℝ vecNormSq x := by
  unfold vecNormSq vecDot
  fun_prop

private theorem differentiableAt_vecNormSq_rpow_vector
    {d : ℕ} (s : ℝ) (x : Vec d) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : Vec d => (vecNormSq y) ^ s) x := by
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  exact (differentiableAt_vecNormSq_vector x).rpow_const (Or.inl hR)

private theorem classicalGradient_radialVectorField_component
    {d : ℕ} (a b s : ℝ) (k i : Fin d) (x : Vec d) (hx : x ≠ 0) :
    classicalGradient (fun y : Vec d => radialVectorField a b s k y i) x =
      fun j =>
        a * basisVec k i *
            (s * (vecNormSq x) ^ (s - 1) * (2 * x j)) +
          b * (((if j = k then x i else 0) +
              (if j = i then x k else 0)) *
                (vecNormSq x) ^ (s - 1) +
            x k * x i *
              ((s - 1) * (vecNormSq x) ^ (s - 2) * (2 * x j))) := by
  have hqS := differentiableAt_vecNormSq_rpow_vector s x hx
  have hqSm := differentiableAt_vecNormSq_rpow_vector (s - 1) x hx
  have hk := (hasFDerivAt_apply (𝕜 := ℝ) k x).differentiableAt
  have hi := (hasFDerivAt_apply (𝕜 := ℝ) i x).differentiableAt
  have hfirst := classicalGradient_vecNormSq_rpow s x hx
  have hsecond :=
    classicalGradient_coordinate_mul_coordinate_mul_vecNormSq_rpow
      k i (s - 1) x hx
  funext j
  rw [classicalGradient_apply]
  simp only [radialVectorField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hfun :
      (fun y : Vec d =>
        a * (vecNormSq y) ^ s * basisVec k i +
          b * y k * (vecNormSq y) ^ (s - 1) * y i) =
        fun y =>
          (a * basisVec k i) * (vecNormSq y) ^ s +
            b * (y k * y i * (vecNormSq y) ^ (s - 1)) := by
    funext y
    ring
  rw [hfun]
  have hdiffFirst : DifferentiableAt ℝ
      (fun y : Vec d => (a * basisVec k i) * (vecNormSq y) ^ s) x :=
    hqS.const_mul _
  have hdiffSecond : DifferentiableAt ℝ
      (fun y : Vec d => b * (y k * y i * (vecNormSq y) ^ (s - 1))) x :=
    ((hk.mul hi).mul hqSm).const_mul _
  have hadd : fderiv ℝ
      (fun y : Vec d =>
        (a * basisVec k i) * (vecNormSq y) ^ s +
          b * (y k * y i * (vecNormSq y) ^ (s - 1))) x =
      fderiv ℝ (fun y : Vec d =>
        (a * basisVec k i) * (vecNormSq y) ^ s) x +
      fderiv ℝ (fun y : Vec d =>
        b * (y k * y i * (vecNormSq y) ^ (s - 1))) x := by
    simpa only [Pi.add_apply] using! fderiv_add hdiffFirst hdiffSecond
  have hconstFirst : fderiv ℝ
      (fun y : Vec d => (a * basisVec k i) * (vecNormSq y) ^ s) x =
      (a * basisVec k i) •
        fderiv ℝ (fun y : Vec d => (vecNormSq y) ^ s) x :=
    fderiv_const_mul hqS _
  have hconstSecond : fderiv ℝ
      (fun y : Vec d => b * (y k * y i * (vecNormSq y) ^ (s - 1))) x =
      b • fderiv ℝ
        (fun y : Vec d => y k * y i * (vecNormSq y) ^ (s - 1)) x := by
    simpa only [Pi.mul_apply] using!
      fderiv_const_mul ((hk.mul hi).mul hqSm) b
  rw [hadd, hconstFirst, hconstSecond]
  simp only [add_apply, smul_apply,
    smul_eq_mul, ← classicalGradient_apply]
  rw [hfirst, hsecond]
  ring_nf

/-- Exact divergence of a two-term coordinate radial vector field, away from
the origin. -/
theorem sum_classicalGradient_radialVectorField_component
    {d : ℕ} (a b s : ℝ) (k : Fin d) (x : Vec d) (hx : x ≠ 0) :
    (∑ i : Fin d,
      classicalGradient (fun y : Vec d => radialVectorField a b s k y i) x i) =
      (2 * a * s + b * ((d : ℝ) + 2 * s - 1)) *
        x k * (vecNormSq x) ^ (s - 1) := by
  simp_rw [classicalGradient_radialVectorField_component a b s k _ x hx]
  have hR : vecNormSq x ≠ 0 :=
    fun h => hx (vecNormSq_eq_zero h)
  have hRpos : 0 < vecNormSq x :=
    lt_of_le_of_ne (vecNormSq_nonneg x) (Ne.symm hR)
  simp only [Finset.sum_add_distrib]
  have hbasis :
      (∑ i : Fin d, a * basisVec k i *
        (s * (vecNormSq x) ^ (s - 1) * (2 * x i))) =
        2 * a * s * x k * (vecNormSq x) ^ (s - 1) := by
    rw [Finset.sum_eq_single k]
    · simp [basisVec_apply]
      ring
    · intro i _hi hik
      simp [basisVec_apply, hik]
    · simp
  rw [hbasis]
  simp only [ite_eq_left]
  have hlinear :
      (∑ i : Fin d,
        (((if i = k then x i else 0) + x k) *
            (vecNormSq x) ^ (s - 1))) =
        ((d : ℝ) + 1) * x k * (vecNormSq x) ^ (s - 1) := by
    rw [← Finset.sum_mul]
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hi : (∑ i : Fin d, if i = k then x i else 0) = x k := by simp
    rw [hi]
    ring
  have hquad :
      (∑ i : Fin d, x k * x i *
        ((s - 1) * (vecNormSq x) ^ (s - 2) * (2 * x i))) =
        2 * (s - 1) * x k * (vecNormSq x) ^ (s - 1) := by
    rw [show (∑ i : Fin d, x k * x i *
        ((s - 1) * (vecNormSq x) ^ (s - 2) * (2 * x i))) =
        (2 * (s - 1) * x k * (vecNormSq x) ^ (s - 2)) *
          ∑ i : Fin d, x i * x i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
    rw [show (∑ i : Fin d, x i * x i) = vecNormSq x by rfl]
    rw [show s - 2 = (s - 1) - 1 by ring,
      Real.rpow_sub_one hR (s - 1)]
    field_simp
  rw [show (∑ i : Fin d,
      b * (((if i = k then x i else 0) + x k) *
        (vecNormSq x) ^ (s - 1) +
      x k * x i *
        ((s - 1) * (vecNormSq x) ^ (s - 2) * (2 * x i)))) =
      b * (∑ i : Fin d, ((if i = k then x i else 0) + x k) *
        (vecNormSq x) ^ (s - 1)) +
      b * (∑ i : Fin d, x k * x i *
        ((s - 1) * (vecNormSq x) ^ (s - 2) * (2 * x i))) by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]]
  rw [hlinear, hquad]
  ring

end PDE
