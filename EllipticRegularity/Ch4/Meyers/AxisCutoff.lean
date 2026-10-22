module

public import EllipticRegularity.Ch4.Meyers.Calculus

/-!
# A cutoff vanishing near the codimension-two set `{s = 0}`

`axisCutoff w ε x = θ((s(x)/ε² - 1)/3)` with `θ` the canonical smooth transition. It vanishes on
`{s ≤ ε²}`, equals one on `{s ≥ 4ε²}`, and its gradient is bounded by `11/ε` and supported in
`{s ≤ 4ε²}`.
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

/-- The cutoff vanishing near the singular set. -/
noncomputable def axisCutoff (w : Fin d → ℝ) (ε : ℝ) (x : Vec d) : ℝ :=
  smoothTransitionProfile ((1 / (3 * ε ^ 2)) * axisSq w x - 1 / 3)

theorem axisCutoff_smooth (w : Fin d → ℝ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (axisCutoff w ε) := by
  unfold axisCutoff
  refine smoothTransitionProfile.smooth.comp ?_
  exact (((contDiff_axisSq w).const_smul (1 / (3 * ε ^ 2))).sub contDiff_const)

theorem axisCutoff_nonneg (w : Fin d → ℝ) (ε : ℝ) (x : Vec d) : 0 ≤ axisCutoff w ε x :=
  smoothTransitionProfile.nonneg _

theorem axisCutoff_le_one (w : Fin d → ℝ) (ε : ℝ) (x : Vec d) : axisCutoff w ε x ≤ 1 :=
  smoothTransitionProfile.le_one _

theorem axisCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {x : Vec d} (h : axisSq w x ≤ ε ^ 2) :
    axisCutoff w ε x = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  have : (1 / (3 * ε ^ 2)) * axisSq w x ≤ (1 / (3 * ε ^ 2)) * ε ^ 2 :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : (1 / (3 * ε ^ 2)) * ε ^ 2 = 1 / 3 := by field_simp
  linarith

theorem axisCutoff_eq_one {ε : ℝ} (hε : 0 < ε) {x : Vec d} (h : 4 * ε ^ 2 ≤ axisSq w x) :
    axisCutoff w ε x = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  have : (1 / (3 * ε ^ 2)) * (4 * ε ^ 2) ≤ (1 / (3 * ε ^ 2)) * axisSq w x :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : (1 / (3 * ε ^ 2)) * (4 * ε ^ 2) = 4 / 3 := by field_simp
  linarith

theorem axisCutoff_tendsto_one {x : Vec d} (hx : 0 < axisSq w x) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => axisCutoff w (ε n) x) Filter.atTop (nhds 1) := by
  have hsq : Filter.Tendsto (fun n => 4 * ε n ^ 2) Filter.atTop (nhds 0) := by
    have := (hε0.pow 2).const_mul 4
    simpa using this
  have hev : ∀ᶠ n in Filter.atTop, 4 * ε n ^ 2 < axisSq w x :=
    (tendsto_order.1 hsq).2 _ hx
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hev] with n hn
  exact axisCutoff_eq_one (hε n) hn.le

theorem hasFDerivAt_axisCutoff {ε : ℝ} (x : Vec d) :
    HasFDerivAt (axisCutoff w ε)
      ((deriv smoothTransitionProfile ((1 / (3 * ε ^ 2)) * axisSq w x - 1 / 3)) •
        ((1 / (3 * ε ^ 2)) • ∑ j : Fin d, (2 * w j * x j) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin d => ℝ) j)) x := by
  have hθ : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile ((1 / (3 * ε ^ 2)) * axisSq w x - 1 / 3))
      ((1 / (3 * ε ^ 2)) * axisSq w x - 1 / 3) :=
    (smoothTransitionProfile.smooth.differentiable (by simp) _).hasDerivAt
  have ht : HasFDerivAt (fun y : Vec d => (1 / (3 * ε ^ 2)) * axisSq w y - 1 / 3)
      ((1 / (3 * ε ^ 2)) • ∑ j : Fin d, (2 * w j * x j) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin d => ℝ) j) x :=
    ((hasFDerivAt_axisSq w x).const_mul (1 / (3 * ε ^ 2))).sub_const _
  exact hθ.comp_hasFDerivAt x ht

theorem abs_partial_axisCutoff_le (hw : ∀ i, w i = 0 ∨ w i = 1) {ε : ℝ} (hε : 0 < ε)
    (x : Vec d) (i : Fin d) :
    |fderiv ℝ (axisCutoff w ε) x (basisVec i)| ≤
      (11 / ε) * (if axisSq w x ≤ 4 * ε ^ 2 then 1 else 0) := by
  by_cases hs : axisSq w x ≤ 4 * ε ^ 2
  · simp only [hs, ↓reduceIte, mul_one]
    rw [(hasFDerivAt_axisCutoff x).fderiv]
    simp only [smul_apply, smul_eq_mul]
    have hsum : (∑ j : Fin d, (2 * w j * x j) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin d => ℝ) j) (basisVec i) = 2 * w i * x i := by
      simp [basisVec, Pi.single_apply]
    rw [hsum]
    have hd := smoothTransitionProfile.abs_deriv_le_eight
      ((1 / (3 * ε ^ 2)) * axisSq w x - 1 / 3)
    have hwx : |w i * x i| ≤ 2 * ε := by
      refine (abs_wx_le_sqrt hw x i).trans ?_
      rw [show (2 * ε) = Real.sqrt ((2 * ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have e1 : |deriv smoothTransitionProfile ((1 / (3 * ε ^ 2)) * axisSq w x - 1 / 3) *
        (1 / (3 * ε ^ 2) * (2 * w i * x i))| ≤ 8 * (1 / (3 * ε ^ 2) * (2 * (2 * ε))) := by
      rw [abs_mul]
      have : |1 / (3 * ε ^ 2) * (2 * w i * x i)| ≤ 1 / (3 * ε ^ 2) * (2 * (2 * ε)) := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (3 * ε ^ 2))]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show 2 * w i * x i = 2 * (w i * x i) by ring, abs_mul, abs_two]
        linarith
      exact mul_le_mul hd this (abs_nonneg _) (by norm_num)
    refine e1.trans ?_
    rw [show 8 * (1 / (3 * ε ^ 2) * (2 * (2 * ε))) = (32 / 3) / ε by field_simp; ring]
    exact div_le_div_of_nonneg_right (by norm_num) hε.le
  · simp only [hs, ↓reduceIte, mul_zero]
    push Not at hs
    have hopen : IsOpen {y : Vec d | 4 * ε ^ 2 < axisSq w y} :=
      isOpen_lt continuous_const (contDiff_axisSq w).continuous
    have hev : axisCutoff w ε =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [hopen.mem_nhds hs] with y hy
      exact axisCutoff_eq_one hε hy.le
    rw [hev.fderiv_eq]
    simp

end PDE.Ch4Meyers
