module

public import PDEFoundation

/-!
# Morrey growth implies a normalized gradient-scale bound

From the Dirichlet growth `∫_{B_r(x)} |∇u|² ≤ K r^{d-2+2α}` we obtain the normalized
form `r^{1-α} (⨍_{B_r(z)} |∇u|²)^{1/2} ≤ (K / |B_1|)^{1/2}` used by the repository's
interior Campanato theorem.
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory

variable {d : ℕ}

/-- Dirichlet growth gives the normalized gradient-scale bound. -/
theorem morrey_scale_bound {α K : ℝ} (hK : 0 ≤ K)
    (u : H1Function (euclideanBall (0 : Vec d) 1))
    (h : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤ K * r ^ ((d : ℝ) - 2 + 2 * α)) :
    ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      r ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x))) ≤
        Real.sqrt (K / (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
  intro z hz r hr hr2
  set ω := (volume (euclideanBall (0 : Vec d) 1)).toReal with hω
  have hωpos : 0 < ω := volume_euclideanBall_toReal_pos _ (by norm_num)
  have hvol : (volume (euclideanBall z r)).toReal = r ^ d * ω :=
    volume_euclideanBall_toReal_eq_unit_mul_of_pos z hr
  have hrd : 0 < r ^ d * ω := by positivity
  have hI := h z hz r hr hr2
  have hsq : r ^ ((d : ℝ) - 2 + 2 * α) = r ^ d * (r ^ (α - 1)) ^ 2 := by
    rw [← Real.rpow_natCast (r ^ (α - 1)) 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r d,
      ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have havg : integralAverage (euclideanBall z r) (fun x => vecNormSq (u.grad x)) ≤
      K / ω * (r ^ (α - 1)) ^ 2 := by
    unfold integralAverage
    rw [hvol]
    calc (r ^ d * ω)⁻¹ * ∫ x in euclideanBall z r, vecNormSq (u.grad x)
        ≤ (r ^ d * ω)⁻¹ * (K * (r ^ d * (r ^ (α - 1)) ^ 2)) := by
          rw [hsq] at hI
          exact mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hrd.le)
      _ = K / ω * (r ^ (α - 1)) ^ 2 := by
          field_simp
  have hs : Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (u.grad x))) ≤
      Real.sqrt (K / ω) * r ^ (α - 1) := by
    calc _ ≤ Real.sqrt (K / ω * (r ^ (α - 1)) ^ 2) := Real.sqrt_le_sqrt havg
      _ = Real.sqrt (K / ω) * r ^ (α - 1) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.rpow_nonneg hr.le _)]
  calc r ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x)))
      ≤ r ^ (1 - α) * (Real.sqrt (K / ω) * r ^ (α - 1)) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hr.le _)
    _ = Real.sqrt (K / ω) := by
        have : r ^ (1 - α) * r ^ (α - 1) = 1 := by
          rw [← Real.rpow_add hr]; simp
        calc _ = Real.sqrt (K / ω) * (r ^ (1 - α) * r ^ (α - 1)) := by ring
          _ = _ := by rw [this, mul_one]

end PDE.Ch4Planar
