module

public import PDEFoundation.Monotonicity.ACF.WeightedWeakSub
public import PDEFoundation.Monotonicity.ACF.WeightedRpow
public import PDEFoundation.Monotonicity.ACF.WeightedCutoff

/-!
# The regularized weighted test: `ε > 0`

With `κ = (d-2)/2`, `Z = acfCut r k` and `Ψ_ε(s) = (s + ε²)^{-κ} Z(s) θ_ε(s)` (the factor `θ_ε`
is `1` for `s ≥ -ε²/4` and `0` for `s ≤ -ε²/2`; it only makes `Ψ_ε` globally smooth), the
weighted sub-mean inequality gives

`∫ Ψ_ε(|x|²) |∇u|² ≤ ½ ∫ u² T_ε(|x|²)`,

where `T_ε(s) = Z'(s) (2 d Q_ε + 8 s Q_ε') + 4 s Q_ε Z''(s)`, because the term of `Δ g_ε ≤ 0`
has a favourable sign.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

/-- `κ = (d-2)/2`. -/
def acfKappa (d : ℕ) : ℝ := ((d : ℝ) - 2) / 2

theorem acfKappa_eq (d : ℕ) : (d : ℝ) = 2 * acfKappa d + 2 := by
  unfold acfKappa; ring

theorem acfKappa_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ acfKappa d := by
  unfold acfKappa
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- The extra factor making `Ψ_ε` globally smooth. -/
def acfTheta (ε s : ℝ) : ℝ := Real.smoothTransition (4 * s / ε ^ 2 + 2)

/-- The test profile `Ψ_ε(s) = (s + ε²)^{-κ} Z(s) θ_ε(s)`. -/
def acfPsi (κ r k ε s : ℝ) : ℝ := acfQ κ ε s * acfCut r k s * acfTheta ε s

/-- The explicit upper bound `T_ε`. -/
def acfT (d : ℕ) (r k ε s : ℝ) : ℝ :=
  deriv (acfCut r k) s * (2 * d * acfQ (acfKappa d) ε s + 8 * s * acfQ1 (acfKappa d) ε s) +
    4 * s * acfQ (acfKappa d) ε s * deriv (deriv (acfCut r k)) s

theorem acfTheta_eq_one {ε s : ℝ} (hs : -(ε ^ 2) / 4 ≤ s) (hε : ε ≠ 0) : acfTheta ε s = 1 := by
  unfold acfTheta
  apply Real.smoothTransition.one_of_one_le
  have h : 0 < ε ^ 2 := by positivity
  rw [← sub_nonneg]
  have : 4 * s / ε ^ 2 + 2 - 1 = (4 * s + ε ^ 2) / ε ^ 2 := by field_simp; ring
  rw [this]
  exact div_nonneg (by linarith) h.le

theorem acfTheta_eq_zero {ε s : ℝ} (hs : s ≤ -(ε ^ 2) / 2) (hε : ε ≠ 0) : acfTheta ε s = 0 := by
  unfold acfTheta
  apply Real.smoothTransition.zero_of_nonpos
  have h : 0 < ε ^ 2 := by positivity
  have : 4 * s / ε ^ 2 + 2 = (4 * s + 2 * ε ^ 2) / ε ^ 2 := by field_simp
  rw [this]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) h.le

variable {r k κ : ℝ}

theorem contDiff_acfPsi (hr : 0 < r) (hk : 0 < k) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (acfPsi κ r k ε) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hε2 : 0 < ε ^ 2 := by positivity
  by_cases hs : -(ε ^ 2) < s
  · have hQ : ContDiffAt ℝ (⊤ : ℕ∞) (acfQ κ ε) s := by
      unfold acfQ
      exact (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (by simp only [id]; linarith)
    have hθ : ContDiffAt ℝ (⊤ : ℕ∞) (acfTheta ε) s := by
      unfold acfTheta
      have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 4 * s / ε ^ 2 + 2) :=
        ((contDiff_const.mul contDiff_id).div_const _).add contDiff_const
      exact (Real.smoothTransition.contDiff.comp hlin).contDiffAt
    exact (hQ.mul (contDiff_acfCut hr hk).contDiffAt).mul hθ
  · have : acfPsi κ r k ε =ᶠ[nhds s] fun _ => 0 := by
      filter_upwards [gt_mem_nhds (show s < -(ε ^ 2) / 2 by linarith [not_lt.mp hs])] with t ht
      unfold acfPsi
      rw [acfTheta_eq_zero ht.le hε]; ring
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem acfPsi_eq_zero (hk : 0 < k) {ε s : ℝ} (hs : (r + k) ^ 2 ≤ s) : acfPsi κ r k ε s = 0 := by
  unfold acfPsi
  rw [acfCut_eq_zero hk hs]; ring

theorem acfPsi_nonneg {ε s : ℝ} (hε : ε ≠ 0) (hs : 0 ≤ s) : 0 ≤ acfPsi κ r k ε s := by
  have hε2 : 0 < ε ^ 2 := by positivity
  unfold acfPsi
  have h1 := acfQ_nonneg (κ := κ) (by linarith : 0 ≤ s + ε ^ 2)
  have h2 := acfCut_nonneg (r := r) (k := k) s
  have h3 : 0 ≤ acfTheta ε s := Real.smoothTransition.nonneg _
  positivity

/-- Near `s ≥ 0` the factor `θ_ε` is `1`. -/
theorem acfPsi_eventuallyEq {ε s : ℝ} (hε : ε ≠ 0) (hs : 0 ≤ s) :
    acfPsi κ r k ε =ᶠ[nhds s] fun t => acfQ κ ε t * acfCut r k t := by
  have hε2 : 0 < ε ^ 2 := by positivity
  filter_upwards [lt_mem_nhds (show -(ε ^ 2) / 4 < s by linarith)] with t ht
  unfold acfPsi
  rw [acfTheta_eq_one ht.le hε, mul_one]

theorem hasDerivAt_acfCut_deriv (hr : 0 < r) (hk : 0 < k) (s : ℝ) :
    HasDerivAt (acfCut r k) (deriv (acfCut r k) s) s :=
  (((contDiff_acfCut hr hk).differentiable (by simp)) s).hasDerivAt

theorem hasDerivAt_acfCut_deriv_deriv (hr : 0 < r) (hk : 0 < k) (s : ℝ) :
    HasDerivAt (deriv (acfCut r k)) (deriv (deriv (acfCut r k)) s) s :=
  (((contDiff_infty_iff_deriv.mp (contDiff_acfCut hr hk)).2.differentiable (by simp)) s).hasDerivAt

theorem acfPsi_deriv (hr : 0 < r) (hk : 0 < k) {ε s : ℝ} (hε : ε ≠ 0) (hs : 0 ≤ s) :
    deriv (acfPsi κ r k ε) s =
      acfQ1 κ ε s * acfCut r k s + acfQ κ ε s * deriv (acfCut r k) s ∧
    deriv (deriv (acfPsi κ r k ε)) s =
      acfQ2 κ ε s * acfCut r k s + 2 * acfQ1 κ ε s * deriv (acfCut r k) s +
        acfQ κ ε s * deriv (deriv (acfCut r k)) s := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hP : ∀ t, 0 < t + ε ^ 2 → HasDerivAt (fun t => acfQ κ ε t * acfCut r k t)
      (acfQ1 κ ε t * acfCut r k t + acfQ κ ε t * deriv (acfCut r k) t) t := fun t ht =>
    (hasDerivAt_acfQ (κ := κ) ht).mul (hasDerivAt_acfCut_deriv hr hk t)
  have hE : HasDerivAt (fun t => acfQ1 κ ε t * acfCut r k t + acfQ κ ε t * deriv (acfCut r k) t)
      (acfQ2 κ ε s * acfCut r k s + 2 * acfQ1 κ ε s * deriv (acfCut r k) s +
        acfQ κ ε s * deriv (deriv (acfCut r k)) s) s := by
    have h := ((hasDerivAt_acfQ1 (κ := κ) (by linarith : 0 < s + ε ^ 2)).mul
      (hasDerivAt_acfCut_deriv hr hk s)).add
      ((hasDerivAt_acfQ (κ := κ) (by linarith : 0 < s + ε ^ 2)).mul
        (hasDerivAt_acfCut_deriv_deriv hr hk s))
    refine h.congr_deriv ?_
    ring
  have hev1 : acfPsi κ r k ε =ᶠ[nhds s] fun t => acfQ κ ε t * acfCut r k t :=
    acfPsi_eventuallyEq hε hs
  have hev2 : deriv (fun t => acfQ κ ε t * acfCut r k t) =ᶠ[nhds s]
      fun t => acfQ1 κ ε t * acfCut r k t + acfQ κ ε t * deriv (acfCut r k) t := by
    filter_upwards [lt_mem_nhds (show -(ε ^ 2) < s by linarith)] with t ht
    exact (hP t (by linarith)).deriv
  have hev3 : deriv (acfPsi κ r k ε) =ᶠ[nhds s]
      fun t => acfQ1 κ ε t * acfCut r k t + acfQ κ ε t * deriv (acfCut r k) t :=
    hev1.deriv.trans hev2
  refine ⟨?_, ?_⟩
  · rw [hev3.self_of_nhds]
  · rw [hev3.deriv_eq]
    exact hE.deriv

/-- Pointwise comparison with the explicit bound `T_ε`. -/
theorem acfPsi_laplacian_le (hr : 0 < r) (hk : 0 < k) {d : ℕ} (hd : 2 ≤ d) {ε s : ℝ} (hε : ε ≠ 0)
    (hs : 0 ≤ s) :
    2 * d * deriv (acfPsi (acfKappa d) r k ε) s +
        4 * s * deriv (deriv (acfPsi (acfKappa d) r k ε)) s ≤ acfT d r k ε s := by
  have hε2 : 0 < ε ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := acfPsi_deriv (κ := acfKappa d) hr hk hε hs
  rw [h1, h2]
  have hlap := acf_laplace_Q_nonpos (κ := acfKappa d) (ε := ε) (s := s) (d := (d : ℝ))
    (acfKappa_eq d) (acfKappa_nonneg hd) (by linarith)
  have hZ := mul_nonpos_of_nonneg_of_nonpos (acfCut_nonneg (r := r) (k := k) s) hlap
  unfold acfT
  nlinarith only [hZ]

/-- Integrability of `u² · G(|x|²)` for `G` continuous on `[0, ∞)` and compactly supported. -/
theorem integrableOn_sq_mul_radial {d : ℕ} {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hG0 : ∀ s, ρ ^ 2 < s → G s = 0) :
    IntegrableOn (fun x => u.toFun x ^ 2 * G (vecNormSq x)) (euclideanBall (0 : Vec d) R) := by
  have hu2 : IntegrableOn (fun x => u.toFun x ^ 2) (euclideanBall (0 : Vec d) R) :=
    (show MemLp u.toFun 2 (volume.restrict (euclideanBall (0 : Vec d) R)) from
      u.memL2).integrable_sq
  have hcont : Continuous (fun x : Vec d => G (vecNormSq x)) :=
    hG.comp_continuous continuous_vecNormSq (fun x => vecNormSq_nonneg x)
  have hcs : HasCompactSupport (fun x : Vec d => G (vecNormSq x)) := by
    refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hρ) ?_
    intro x hx
    rw [mem_euclideanClosedBall_zero_iff, not_le] at hx
    exact hG0 _ hx
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  exact Integrable.mul_bdd (c := C) hu2 hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using hC x)

theorem deriv_eq_zero_of_gt {K : ℝ → ℝ} {ρ : ℝ} (hK0 : ∀ s, ρ < s → K s = 0) {s : ℝ}
    (hs : ρ < s) : deriv K s = 0 := by
  have : K =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hs] with t ht using hK0 t ht
  rw [this.deriv_eq]; simp

end

end PDE
