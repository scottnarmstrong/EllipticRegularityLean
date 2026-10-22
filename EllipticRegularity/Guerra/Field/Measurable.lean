module

public import EllipticRegularity.Guerra.Field.Basic

/-!
# Guerra sharpness: measurability and boundedness of the matrix field `B`
-/

@[expose] public section

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

theorem measurable_rad : Measurable (rad : Vec d → ℝ) := measurable_vecEuclideanNorm

theorem measurable_omega_apply (i : Fin d) : Measurable (fun x : Vec d => omega x i) := by
  simp only [omega, Pi.smul_apply, smul_eq_mul]
  exact measurable_rad.inv.mul (measurable_pi_apply i)

theorem measurable_lat (j : Fin d) : Measurable (lat j : Vec d → ℝ) := by
  unfold lat
  exact (measurable_pi_apply j).div measurable_rad

theorem measurable_qvec_apply (j i : Fin d) : Measurable (fun x : Vec d => qvec j x i) := by
  simp only [qvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  exact measurable_const.sub ((measurable_lat j).mul (measurable_omega_apply i))

theorem measurable_yvec_apply {h : ℝ → ℝ} (hh : Measurable h) (j i : Fin d) :
    Measurable (fun x : Vec d => yvec h j x i) := by
  simp only [yvec, Pi.smul_apply, smul_eq_mul]
  exact (hh.comp (measurable_lat j)).mul (measurable_qvec_apply j i)

/-- Entrywise measurability of the matrix field. -/
theorem measurable_fieldMatrix_apply {γ : ℝ} {h : ℝ → ℝ} (hh : Measurable h) (j i k : Fin d) :
    Measurable (fun x : Vec d => fieldMatrix γ h j x i k) := by
  simp only [fieldMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  exact ((measurable_const.add
    (measurable_const.mul ((measurable_omega_apply i).mul (measurable_omega_apply k)))).add
    ((measurable_omega_apply i).mul (measurable_yvec_apply hh j k)))

theorem abs_omega_apply_le (x : Vec d) (i : Fin d) : |omega x i| ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp [omega_zero]
  · have hr := rad_pos hx
    have := abs_apply_le_vecEuclideanNorm x i
    simp only [omega, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hr]
    rw [inv_mul_le_iff₀ hr]
    simpa [rad] using this

/-- Boundedness of the matrix field: `|B_{ik}| ≤ 1 + b + 20γ` when `|h| ≤ 10γ`. -/
theorem abs_fieldMatrix_apply_le {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j i k : Fin d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (x : Vec d) :
    |fieldMatrix γ h j x i k| ≤ 1 + bcoef γ + 20 * γ := by
  have hb : 0 ≤ bcoef γ := by unfold bcoef; positivity
  have hi := abs_omega_apply_le x i
  have hk := abs_omega_apply_le x k
  have ht := abs_lat_le_one j x
  have hY : |yvec h j x k| ≤ 20 * γ := by
    simp only [yvec, Pi.smul_apply, smul_eq_mul, abs_mul]
    have h1 := hh _ ht
    have h2 : |qvec j x k| ≤ 2 := by
      simp only [qvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
      refine (abs_sub _ _).trans ?_
      have : |(if k = j then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      rw [abs_mul]
      nlinarith [abs_nonneg (lat j x), abs_nonneg (omega x k)]
    nlinarith [abs_nonneg (h (lat j x)), abs_nonneg (qvec j x k)]
  simp only [fieldMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  have hone : |(1 : Mat d) i k| ≤ 1 := by
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik]
  have h2 : |(bcoef γ - 1) * (omega x i * omega x k)| ≤ bcoef γ := by
    rw [abs_mul, abs_mul]
    have : |bcoef γ - 1| ≤ bcoef γ := by
      rw [abs_le]; constructor <;> nlinarith [show 1 ≤ bcoef γ by unfold bcoef; nlinarith]
    have h3 : |omega x i| * |omega x k| ≤ 1 := by
      nlinarith [abs_nonneg (omega x i), abs_nonneg (omega x k)]
    nlinarith [abs_nonneg (omega x i), abs_nonneg (omega x k), abs_nonneg (bcoef γ - 1),
      mul_nonneg (abs_nonneg (omega x i)) (abs_nonneg (omega x k))]
  have h4 : |omega x i * yvec h j x k| ≤ 20 * γ := by
    rw [abs_mul]
    nlinarith [abs_nonneg (omega x i), abs_nonneg (yvec h j x k)]
  calc _ ≤ |(1 : Mat d) i k + (bcoef γ - 1) * (omega x i * omega x k)| +
        |omega x i * yvec h j x k| := abs_add_le _ _
    _ ≤ (|(1 : Mat d) i k| + |(bcoef γ - 1) * (omega x i * omega x k)|) +
        |omega x i * yvec h j x k| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

end

end PDE.Guerra
