module

public import PDEFoundation.Monotonicity.ACF.WeightedTest

/-!
# The `ε`-regularized weighted inequality

For `ε > 0`: `∫ Ψ_ε(|x|²) |∇u|² ≤ ½ ∫ u² T_ε(|x|²)` over `B_R`, with both sides finite.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {r k κ ε : ℝ}

theorem continuousOn_acfQ (hε : ε ≠ 0) : ContinuousOn (acfQ κ ε) (Ici 0) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  unfold acfQ
  exact (continuousAt_id.add continuousAt_const).rpow_const
    (Or.inl (ne_of_gt (by have : (0 : ℝ) ≤ s := hs; show 0 < s + ε ^ 2; linarith)))

theorem continuousOn_acfQ1 (hε : ε ≠ 0) : ContinuousOn (acfQ1 κ ε) (Ici 0) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  unfold acfQ1
  exact continuousAt_const.mul ((continuousAt_id.add continuousAt_const).rpow_const
    (Or.inl (ne_of_gt (by have : (0 : ℝ) ≤ s := hs; show 0 < s + ε ^ 2; linarith))))

theorem continuousOn_acfT {d : ℕ} (hr : 0 < r) (hk : 0 < k) (hε : ε ≠ 0) :
    ContinuousOn (acfT d r k ε) (Ici 0) := by
  have h1 : Continuous (deriv (acfCut r k)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_acfCut hr hk)).2.continuous
  have h2 : Continuous (deriv (deriv (acfCut r k))) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp (contDiff_acfCut hr hk)).2).2).continuous
  have hQ := continuousOn_acfQ (κ := acfKappa d) hε
  have hQ1 := continuousOn_acfQ1 (κ := acfKappa d) hε
  unfold acfT
  exact (h1.continuousOn.mul ((continuousOn_const.mul hQ).add
    ((continuousOn_const.mul continuousOn_id).mul hQ1))).add
    (((continuousOn_const.mul continuousOn_id).mul hQ).mul h2.continuousOn)

theorem acfT_eq_zero {d : ℕ} (hr : 0 < r) (hk : 0 < k) {s : ℝ} (h : s < r ^ 2 ∨ (r + k) ^ 2 < s) :
    acfT d r k ε s = 0 := by
  unfold acfT
  rcases h with h | h
  · rw [deriv_acfCut_eq_zero_of_lt hr hk h, deriv_deriv_acfCut_eq_zero_of_lt hr hk h]; ring
  · rw [deriv_acfCut_eq_zero_of_gt hk h, deriv_deriv_acfCut_eq_zero_of_gt hk h]; ring

/-- **The `ε`-regularized weighted inequality.** -/
theorem acfTest_inequality {d : ℕ} (hd : 3 ≤ d) {R : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hrk : r + k < R) (hε : 0 < ε) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) :
    IntegrableOn (fun x => acfPsi (acfKappa d) r k ε (vecNormSq x) * vecNormSq (u.grad x))
        (euclideanBall (0 : Vec d) R) ∧
      ∫ x in euclideanBall (0 : Vec d) R,
          acfPsi (acfKappa d) r k ε (vecNormSq x) * vecNormSq (u.grad x) ≤
        (1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x ^ 2 * acfT d r k ε (vecNormSq x) := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hΨ := contDiff_acfPsi (κ := acfKappa d) hr hk hε0
  have hrk0 : 0 < r + k := by linarith
  obtain ⟨hint, hle⟩ := weighted_sub_inequality u hcont hnonneg hsub hΨ hrk0 hrk
    (fun s hs => acfPsi_eq_zero hk hs) (fun s hs => acfPsi_nonneg hε0 hs)
  refine ⟨hint, hle.trans ?_⟩
  have hρ0 : ∀ s, (r + k) ^ 2 < s → acfPsi (acfKappa d) r k ε s = 0 :=
    fun s hs => acfPsi_eq_zero hk hs.le
  have hd1 : ∀ s, (r + k) ^ 2 < s → deriv (acfPsi (acfKappa d) r k ε) s = 0 :=
    fun s hs => deriv_eq_zero_of_gt hρ0 hs
  have hd2 : ∀ s, (r + k) ^ 2 < s → deriv (deriv (acfPsi (acfKappa d) r k ε)) s = 0 :=
    fun s hs => deriv_eq_zero_of_gt hd1 hs
  have hc1 : Continuous (deriv (acfPsi (acfKappa d) r k ε)) :=
    (contDiff_infty_iff_deriv.mp hΨ).2.continuous
  have hc2 : Continuous (deriv (deriv (acfPsi (acfKappa d) r k ε))) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hΨ).2).2).continuous
  have hA := integrableOn_sq_mul_radial u
    (G := fun s => 2 * d * deriv (acfPsi (acfKappa d) r k ε) s +
      4 * s * deriv (deriv (acfPsi (acfKappa d) r k ε)) s)
    (((continuous_const.mul hc1).add ((continuous_const.mul continuous_id).mul hc2)).continuousOn)
    hrk0.le (fun s hs => by simp [hd1 s hs, hd2 s hs])
  have hB := integrableOn_sq_mul_radial u (G := acfT d r k ε)
    (continuousOn_acfT hr hk hε0) hrk0.le (fun s hs => acfT_eq_zero hr hk (Or.inr hs))
  have hmono : ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 *
        (2 * d * deriv (acfPsi (acfKappa d) r k ε) (vecNormSq x) +
          4 * vecNormSq x * deriv (deriv (acfPsi (acfKappa d) r k ε)) (vecNormSq x)) ≤
      ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 * acfT d r k ε (vecNormSq x) := by
    refine setIntegral_mono_on hA hB (isOpen_euclideanBall (0 : Vec d) R).measurableSet ?_
    intro x _
    exact mul_le_mul_of_nonneg_left
      (acfPsi_laplacian_le hr hk (by omega) hε0 (vecNormSq_nonneg x)) (sq_nonneg _)
  linarith

end

end PDE
