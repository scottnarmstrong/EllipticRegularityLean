module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.Lower

/-!
# Friedland--Hayman: the one-variable profile of a height-monotone function

A continuous function `k` on the sphere which is monotone in the height `⟪x, e₀⟫` and Lipschitz
is `k x = h (arccos ⟪x, e₀⟫)` for a Lipschitz function `h : ℝ → ℝ`, obtained by restricting `k` to
the meridian `φ ↦ cos φ e₀ + sin φ e₁` (with the angle clamped to `[0, π]`).
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ} [NeZero D]

/-- The second coordinate vector. -/
def e1 (hD : 2 ≤ D) : HilbertVec D := bas D ⟨1, by omega⟩

omit [NeZero D] in
theorem norm_e1 (hD : 2 ≤ D) : ‖e1 hD‖ = 1 := norm_bas _

theorem inner_e1_pole (hD : 2 ≤ D) : inner ℝ (e1 hD) (pole D) = 0 :=
  inner_bas_pole (by simp [Fin.ext_iff])

/-- The point of the meridian at angle `φ`, as a vector. -/
def meridianVec (hD : 2 ≤ D) (φ : ℝ) : HilbertVec D :=
  Real.cos φ • pole D + Real.sin φ • e1 hD

theorem norm_meridianVec (hD : 2 ≤ D) (φ : ℝ) : ‖meridianVec hD φ‖ = 1 := by
  have h : ‖meridianVec hD φ‖ ^ 2 = 1 := by
    rw [meridianVec, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
      real_inner_comm, inner_e1_pole, norm_pole, norm_e1]
    simp only [Real.norm_eq_abs, mul_one, mul_zero, add_zero, sq_abs]
    have := Real.sin_sq_add_cos_sq φ
    linarith
  have h0 : 0 ≤ ‖meridianVec hD φ‖ := norm_nonneg _
  nlinarith

/-- The meridian as a map into the sphere. -/
def meridian (hD : 2 ≤ D) (φ : ℝ) : Sph D :=
  ⟨meridianVec hD φ, by simp [norm_meridianVec]⟩

theorem inner_meridian_pole (hD : 2 ≤ D) (φ : ℝ) :
    inner ℝ ((meridian hD φ : Sph D) : HilbertVec D) (pole D) = Real.cos φ := by
  show inner ℝ (meridianVec hD φ) (pole D) = _
  rw [meridianVec, inner_add_left, inner_smul_left, inner_smul_left, inner_e1_pole,
    real_inner_self_eq_norm_sq, norm_pole]
  simp

theorem meridian_lipschitz (hD : 2 ≤ D) : LipschitzWith 2 (meridian hD) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Subtype.dist_eq, dist_eq_norm]
  show ‖meridianVec hD a - meridianVec hD b‖ ≤ _
  have e : meridianVec hD a - meridianVec hD b =
      (Real.cos a - Real.cos b) • pole D + (Real.sin a - Real.sin b) • e1 hD := by
    simp only [meridianVec, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_pole, norm_e1, Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
    mul_one]
  have h1 := Real.abs_cos_sub_cos_le a b
  have h2 := Real.abs_sin_sub_sin_le a b
  rw [Real.dist_eq]
  push_cast
  linarith

/-- Clamping an angle to `[0, π]`. -/
def clampAngle (φ : ℝ) : ℝ := max 0 (min φ Real.pi)

theorem clampAngle_lipschitz : LipschitzWith 1 clampAngle :=
  (LipschitzWith.id.min_const Real.pi).const_max 0

theorem clampAngle_of_mem {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ Real.pi) : clampAngle φ = φ := by
  simp [clampAngle, h0, h1]

theorem clampAngle_of_ge {φ : ℝ} (h : Real.pi ≤ φ) : clampAngle φ = Real.pi := by
  simp [clampAngle, h, Real.pi_pos.le]

theorem neg_one_le_inner (x : Sph D) : -1 ≤ inner ℝ (x : HilbertVec D) (pole D) := by
  have h := abs_real_inner_le_norm (x : HilbertVec D) (pole D)
  rw [norm_pole] at h
  have hx : ‖(x : HilbertVec D)‖ = 1 := by simp
  rw [hx, mul_one] at h
  exact (abs_le.1 h).1

/-- The profile of a height-monotone Lipschitz function. -/
theorem exists_profile (hD : 2 ≤ D) (k : C(Sph D, ℝ)) {L : NNReal} (hL : LipschitzWith L k)
    (hk0 : ∀ x, 0 ≤ k x)
    (hmono : ∀ x y : Sph D, inner ℝ (x : HilbertVec D) (pole D) ≤ inner ℝ (y : HilbertVec D)
      (pole D) → k x ≤ k y) :
    ∃ (h : ℝ → ℝ) (K : NNReal), LipschitzWith K h ∧
      (∀ x : Sph D, k x = h (Real.arccos (inner ℝ (x : HilbertVec D) (pole D)))) ∧
      (∀ φ, 0 ≤ h φ) ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi → h b ≤ h a) ∧
      (∀ φ, Real.pi ≤ φ → h φ = h Real.pi) := by
  set h : ℝ → ℝ := fun φ => k (meridian hD (clampAngle φ)) with hhdef
  refine ⟨h, L * (2 * 1), ?_, ?_, fun φ => hk0 _, ?_, ?_⟩
  · exact hL.comp ((meridian_lipschitz hD).comp clampAngle_lipschitz)
  · intro x
    have h1 : -1 ≤ inner ℝ (x : HilbertVec D) (pole D) := neg_one_le_inner x
    have h2 : inner ℝ (x : HilbertVec D) (pole D) ≤ 1 := inner_le_one x
    set φ := Real.arccos (inner ℝ (x : HilbertVec D) (pole D)) with hφ
    have hc : Real.cos φ = inner ℝ (x : HilbertVec D) (pole D) := Real.cos_arccos h1 h2
    have hcl : clampAngle φ = φ := clampAngle_of_mem (Real.arccos_nonneg _) (Real.arccos_le_pi _)
    have hin : inner ℝ ((meridian hD φ : Sph D) : HilbertVec D) (pole D) =
        inner ℝ (x : HilbertVec D) (pole D) := by rw [inner_meridian_pole, hc]
    show k x = k (meridian hD (clampAngle φ))
    rw [hcl]
    exact le_antisymm (hmono _ _ hin.ge) (hmono _ _ hin.le)
  · intro a b ha hab hb
    show k (meridian hD (clampAngle b)) ≤ k (meridian hD (clampAngle a))
    rw [clampAngle_of_mem ha (hab.trans hb), clampAngle_of_mem (ha.trans hab) hb]
    refine hmono _ _ ?_
    rw [inner_meridian_pole, inner_meridian_pole]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha hb hab
  · intro φ hφ
    show k (meridian hD (clampAngle φ)) = k (meridian hD (clampAngle Real.pi))
    rw [clampAngle_of_ge hφ, clampAngle_of_ge le_rfl]

end Local

end

end PDE.FHLane
