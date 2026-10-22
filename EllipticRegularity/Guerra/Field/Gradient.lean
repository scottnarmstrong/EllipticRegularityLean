module

public import EllipticRegularity.Guerra.Field.Derivatives

/-!
# Guerra sharpness: the solution `u = r^α φ(t)` and its classical gradient

For a differentiable profile `φ`, `u(x) = r^α φ(t)` is smooth on `ℝ^d ∖ {0}` (as smooth as `φ`)
and `∇u = r^{α-1} (α φ(t) ω + φ'(t) q)`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- `u(x) = |x|^α φ(x_j/|x|)` for `x ≠ 0`, `u(0) = 0`. -/
def uFun (α : ℝ) (φ : ℝ → ℝ) (j : Fin d) (x : Vec d) : ℝ :=
  if x = 0 then 0 else rad x ^ α * φ (lat j x)

/-- The gradient `r^{α-1}(α φ(t) ω + φ'(t) q)` (a formula for `x ≠ 0`). -/
def gradU (α : ℝ) (φ : ℝ → ℝ) (j : Fin d) (x : Vec d) : Vec d := fun i =>
  rad x ^ (α - 1) * (α * φ (lat j x) * omega x i + deriv φ (lat j x) * qvec j x i)

theorem uFun_of_ne (α : ℝ) (φ : ℝ → ℝ) (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    uFun α φ j x = rad x ^ α * φ (lat j x) := by
  simp [uFun, hx]

theorem uFun_zero (α : ℝ) (φ : ℝ → ℝ) (j : Fin d) : uFun α φ j (0 : Vec d) = 0 := by
  simp [uFun]

theorem contDiffAt_rad {n : ℕ} {x : Vec d} (hx : x ≠ 0) : ContDiffAt ℝ n (rad : Vec d → ℝ) x := by
  have hne : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
  have h : ContDiffAt ℝ n (fun y : Vec d => vecNormSq y) x :=
    (contDiff_vecNormSq.of_le (by exact_mod_cast le_top)).contDiffAt
  exact h.sqrt hne

theorem contDiffAt_lat {n : ℕ} (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    ContDiffAt ℝ n (lat j : Vec d → ℝ) x := by
  unfold lat
  exact (contDiff_apply ℝ ℝ j).contDiffAt.div (contDiffAt_rad hx) (rad_pos hx).ne'

theorem contDiffAt_uFun {n : ℕ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ n φ) (α : ℝ) (j : Fin d)
    {x : Vec d} (hx : x ≠ 0) : ContDiffAt ℝ n (uFun α φ j) x := by
  have h : ContDiffAt ℝ n (fun y : Vec d => rad y ^ α * φ (lat j y)) x :=
    ((contDiffAt_rad hx).rpow_const_of_ne (rad_pos hx).ne').mul
      (hφ.contDiffAt.comp x (contDiffAt_lat j hx))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
  exact uFun_of_ne α φ j hy

theorem contDiffOn_uFun {n : ℕ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ n φ) (α : ℝ) (j : Fin d) :
    ContDiffOn ℝ n (uFun α φ j) ({0} : Set (Vec d))ᶜ :=
  fun _ hx => (contDiffAt_uFun hφ α j hx).contDiffWithinAt

/-- The classical gradient of `u` away from the origin. -/
theorem classicalGradient_uFun {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (α : ℝ) (j : Fin d)
    {x : Vec d} (hx : x ≠ 0) : classicalGradient (uFun α φ j) x = gradU α φ j x := by
  have hr := rad_pos hx
  obtain ⟨LR, hLR, hLRv⟩ := hasFDerivAt_rad hx
  obtain ⟨LT, hLT, hLTv⟩ := hasFDerivAt_lat j hx
  have hpow := hLR.rpow_const (p := α) (Or.inl hr.ne')
  have hφT := ((hφ (lat j x)).hasDerivAt).comp_hasFDerivAt x hLT
  have hprod : HasFDerivAt (fun y : Vec d => rad y ^ α * φ (lat j y))
      (rad x ^ α • deriv φ (lat j x) • LT + φ (lat j x) • (α * rad x ^ (α - 1)) • LR) x :=
    hpow.mul hφT
  have hev : (uFun α φ j) =ᶠ[nhds x] fun y : Vec d => rad y ^ α * φ (lat j y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact uFun_of_ne α φ j hy
  funext i
  rw [classicalGradient_apply, hev.fderiv_eq]
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, hLRv, hLTv, vecDot_basisVec_right]
  have hp : rad x ^ (α - 1) = rad x ^ α / rad x := Real.rpow_sub_one hr.ne' α
  simp only [gradU, omega, qvec, lat, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, basisVec_apply,
    hp]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    field_simp
    ring
  · simp only [hij, ite_false, Ne.symm hij]
    field_simp
    ring

theorem gradU_eq_smul (α : ℝ) (φ : ℝ → ℝ) (j : Fin d) (x : Vec d) :
    gradU α φ j x = rad x ^ (α - 1) •
      ((α * φ (lat j x)) • omega x + deriv φ (lat j x) • qvec j x) := by
  funext i; simp [gradU]

/-- `|∇u|² = r^{2α-2}(α² φ² + (1-t²) φ'²)`. -/
theorem vecNormSq_gradU {φ : ℝ → ℝ} (α : ℝ) (j : Fin d) {x : Vec d} (hx : x ≠ 0) :
    vecNormSq (gradU α φ j x) =
      rad x ^ (2 * α - 2) * (α ^ 2 * φ (lat j x) ^ 2 + (1 - lat j x ^ 2) * deriv φ (lat j x) ^ 2) := by
  have hr := rad_pos hx
  have hg := gradU_eq_smul α φ j x
  have hωq := vecDot_omega_qvec hx j
  have hqω : vecDot (qvec j x) (omega x) = 0 := by rw [vecDot_comm]; exact hωq
  have hpow : (rad x ^ (α - 1)) ^ 2 = rad x ^ (2 * α - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  rw [hg, vecNormSq, vecDot_smul_left, vecDot_smul_right, ← vecNormSq, vecNormSq]
  simp only [vecDot_add_left, vecDot_add_right, vecDot_smul_left, vecDot_smul_right,
    vecNormSq_omega hx, hωq, hqω, vecDot_qvec_qvec hx j]
  rw [← hpow]
  ring

/-- `∇u ≠ 0` away from the origin, given `φ' > 0`, `φ(±1) = ±1`, `α > 0`. -/
theorem gradU_ne_zero {φ : ℝ → ℝ} {α : ℝ} (hα : 0 < α) (j : Fin d)
    (hφ' : ∀ t, 0 < deriv φ t) (h1 : φ 1 = 1) (hm1 : φ (-1) = -1) {x : Vec d} (hx : x ≠ 0) :
    gradU α φ j x ≠ 0 := by
  intro h0
  have h := vecNormSq_gradU (φ := φ) α j hx
  rw [h0] at h
  have hz : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
  rw [hz] at h
  have hp : 0 < rad x ^ (2 * α - 2) := Real.rpow_pos_of_pos (rad_pos hx) _
  have hzero : α ^ 2 * φ (lat j x) ^ 2 + (1 - lat j x ^ 2) * deriv φ (lat j x) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hp.ne'
    · exact h'
  have ht2 := lat_sq_le_one j x
  have hd := hφ' (lat j x)
  by_cases hs : lat j x ^ 2 = 1
  · have hpm : lat j x = 1 ∨ lat j x = -1 := by
      have : (lat j x - 1) * (lat j x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    have hφsq : φ (lat j x) ^ 2 = 1 := by
      rcases hpm with h | h <;> rw [h]
      · rw [h1]; norm_num
      · rw [hm1]; norm_num
    rw [hs, hφsq] at hzero
    nlinarith
  · have hlt : lat j x ^ 2 < 1 := lt_of_le_of_ne ht2 hs
    have : 0 < (1 - lat j x ^ 2) * deriv φ (lat j x) ^ 2 :=
      mul_pos (by linarith) (pow_pos hd 2)
    nlinarith [sq_nonneg (α * φ (lat j x))]

end

end PDE.Guerra
