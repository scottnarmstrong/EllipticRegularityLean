module

public import EllipticRegularity.Parabolic.WeakHarnack.WeightedPoincare
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# An explicit radial cutoff and its weighted Poincaré inequality

`radialCutoff d x = ψ(|x|²)` with the smooth profile
`ψ(t) = smoothTransition ((49/64 - t) · 64/13)`, which equals `1` for `t ≤ 9/16` and `0` for
`t ≥ 49/64`.  Hence `ζ = 1` on `B_{3/4}`, `ζ = 0` off `B_{7/8}`, `0 ≤ ζ ≤ 1`, and `ζ²` has centered
round balls as superlevel sets.  This file records these properties together with
`|∇ζ| ≤ C` and the weighted Poincaré inequality for the weight `ζ²`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.WeakHarnack

open PDE

/-- The radial profile of the cutoff, as a function of `|x|²`. -/
noncomputable def cutoffProfile (t : ℝ) : ℝ :=
  Real.smoothTransition ((49 / 64 - t) * (64 / 13))

theorem cutoffProfile_nonneg (t : ℝ) : 0 ≤ cutoffProfile t := Real.smoothTransition.nonneg _

theorem cutoffProfile_le_one (t : ℝ) : cutoffProfile t ≤ 1 := Real.smoothTransition.le_one _

theorem cutoffProfile_eq_one {t : ℝ} (ht : t ≤ 9 / 16) : cutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith)

theorem cutoffProfile_eq_zero {t : ℝ} (ht : 49 / 64 ≤ t) : cutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith)

theorem cutoffProfile_antitone : Antitone cutoffProfile := by
  intro s t hst
  exact Real.smoothTransition.monotone (by nlinarith)

theorem cutoffProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffProfile :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The explicit radial cutoff `ζ`. -/
noncomputable def radialCutoff (d : ℕ) (x : Vec d) : ℝ :=
  cutoffProfile (vecNormSq x)

theorem radialCutoff_nonneg {d : ℕ} (x : Vec d) : 0 ≤ radialCutoff d x :=
  cutoffProfile_nonneg _

theorem radialCutoff_le_one {d : ℕ} (x : Vec d) : radialCutoff d x ≤ 1 :=
  cutoffProfile_le_one _

theorem mem_euclideanBall_zero_iff {d : ℕ} (x : Vec d) (r : ℝ) :
    x ∈ euclideanBall (0 : Vec d) r ↔ vecNormSq x < r ^ 2 := by
  simp [euclideanBall, euclideanSqDist]

/-- `ζ = 1` on `B_{3/4}`. -/
theorem radialCutoff_eq_one {d : ℕ} {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (3 / 4)) :
    radialCutoff d x = 1 := by
  rw [mem_euclideanBall_zero_iff] at hx
  exact cutoffProfile_eq_one (by norm_num at hx; linarith)

/-- `ζ = 0` off `B_{7/8}`. -/
theorem radialCutoff_eq_zero {d : ℕ} {x : Vec d} (hx : x ∉ euclideanBall (0 : Vec d) (7 / 8)) :
    radialCutoff d x = 0 := by
  rw [mem_euclideanBall_zero_iff, not_lt] at hx
  exact cutoffProfile_eq_zero (by norm_num at hx; linarith)

theorem radialCutoff_contDiff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (radialCutoff d) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
    have : (fun x : Vec d => vecNormSq x) = fun x => ∑ i, x i ^ 2 := by
      funext x; exact vecNormSq_eq_sum_sq x
    rw [this]
    fun_prop
  exact cutoffProfile_contDiff.comp h

/-- A continuous antitone profile that drops from `1` at `9/16` to `0` at `49/64` has
superlevel sets that are initial segments with endpoint in `[9/16, 49/64]`. -/
theorem exists_level_threshold {φ : ℝ → ℝ} (hc : Continuous φ) (ha : Antitone φ)
    (h1 : φ (9 / 16) = 1) (h0 : φ (49 / 64) = 0) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ τ : ℝ, 9 / 16 ≤ τ ∧ τ ≤ 49 / 64 ∧ ∀ t, s < φ t ↔ t < τ := by
  set S : Set ℝ := {t | s < φ t} with hS
  have hSopen : IsOpen S := isOpen_lt continuous_const hc
  have hmem : (9 / 16 : ℝ) ∈ S := by simp [hS, h1, hs1]
  have hdown : ∀ t t', t ≤ t' → t' ∈ S → t ∈ S := fun t t' h ht' => lt_of_lt_of_le ht' (ha h)
  have hbdd : ∀ t ∈ S, t < 49 / 64 := by
    intro t ht
    by_contra hge
    have := ha (not_lt.1 hge)
    simp only [hS, mem_ofPred_eq] at ht
    linarith
  have hbd : BddAbove S := ⟨49 / 64, fun t ht => (hbdd t ht).le⟩
  refine ⟨sSup S, le_csSup hbd hmem, csSup_le ⟨_, hmem⟩ fun t ht => (hbdd t ht).le, fun t => ?_⟩
  constructor
  · intro ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSopen t ht
    have : t + ε / 2 ∈ S := hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact lt_of_lt_of_le (by linarith) (le_csSup hbd this)
  · intro ht
    obtain ⟨t', ht', htt'⟩ := exists_lt_of_lt_csSup ⟨_, hmem⟩ ht
    exact hdown t t' htt'.le ht'

/-- The weight `ζ²` has centered balls of radius in `[3/4, 7/8]` as superlevel sets. -/
theorem radialCutoff_sq_isRadialLevelWeight (d : ℕ) :
    IsRadialLevelWeight (fun x : Vec d => radialCutoff d x ^ 2) := by
  intro s hs0 hs1
  have hc : Continuous fun t => cutoffProfile t ^ 2 :=
    (cutoffProfile_contDiff.continuous).pow 2
  have ha : Antitone fun t => cutoffProfile t ^ 2 := fun a b hab =>
    pow_le_pow_left₀ (cutoffProfile_nonneg b) (cutoffProfile_antitone hab) 2
  obtain ⟨τ, hτ1, hτ2, hτ⟩ := exists_level_threshold hc ha
    (by simp [cutoffProfile_eq_one (le_refl (9 / 16 : ℝ))])
    (by simp [cutoffProfile_eq_zero (le_refl (49 / 64 : ℝ))]) hs0 hs1
  have hτ0 : 0 ≤ τ := by linarith
  refine ⟨Real.sqrt τ, ?_, ?_, ?_⟩
  · exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  · rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by linarith⟩
  · ext x
    rw [mem_euclideanBall_zero_iff, Real.sq_sqrt hτ0]
    exact hτ (vecNormSq x)

/-- The cutoff has a bounded gradient: `|∇ζ(x) · v| ≤ C |v|` with an absolute constant `C`. -/
theorem radialCutoff_fderiv_bound (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x v : Vec d,
      |fderiv ℝ (radialCutoff d) x v| ≤ C * vecEuclideanNorm v := by
  have hdiff : Differentiable ℝ cutoffProfile :=
    cutoffProfile_contDiff.differentiable (by simp)
  have hcont : Continuous (deriv cutoffProfile) :=
    (cutoffProfile_contDiff.of_le (by simp : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).continuous_deriv
      le_rfl
  have hzero : ∀ t, deriv cutoffProfile t ≠ 0 → 9 / 16 < t ∧ t < 49 / 64 := by
    intro t ht
    constructor
    · by_contra h
      apply ht
      have h1 : cutoffProfile t = 1 := cutoffProfile_eq_one (not_lt.1 h)
      exact IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall fun y => by
        rw [h1]; exact cutoffProfile_le_one y)
    · by_contra h
      apply ht
      have h1 : cutoffProfile t = 0 := cutoffProfile_eq_zero (not_lt.1 h)
      exact IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun y => by
        rw [h1]; exact cutoffProfile_nonneg y)
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc (a := (9 / 16 : ℝ)) (b := 49 / 64)).exists_bound_of_continuousOn
    hcont.continuousOn
  set L := max L₀ 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  have hbound : ∀ t, |deriv cutoffProfile t| ≤ L := by
    intro t
    by_cases ht : deriv cutoffProfile t = 0
    · rw [ht]; simpa using hL0
    · obtain ⟨h1, h2⟩ := hzero t ht
      exact (hL₀ t ⟨h1.le, h2.le⟩).trans (le_max_left _ _)
  refine ⟨2 * L, by positivity, fun x v => ?_⟩
  -- derivative of `vecNormSq`
  have hq : HasFDerivAt (fun y : Vec d => vecNormSq y)
      (∑ i, (2 * x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) x := by
    have : (fun y : Vec d => vecNormSq y) = fun y => ∑ i, y i * y i := by
      funext y; simp [vecNormSq, vecDot]
    rw [this]
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun i y => y i * y i)
      (A' := fun i => (2 * x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))
      (x := x) fun i _ => by
        have h1 : HasFDerivAt (fun y : Vec d => y i)
            (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) x := hasFDerivAt_apply i x
        have := h1.mul h1
        convert this using 1
        ext v; simp; ring
    exact h
  have hcomp := (hdiff (vecNormSq x)).hasDerivAt.comp_hasFDerivAt x hq
  have hfd : fderiv ℝ (radialCutoff d) x v =
      deriv cutoffProfile (vecNormSq x) * (2 * vecDot x v) := by
    have h : fderiv ℝ (cutoffProfile ∘ vecNormSq) x =
        deriv cutoffProfile (vecNormSq x) • ∑ i, (2 * x i) •
          (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) := hcomp.fderiv
    change fderiv ℝ (cutoffProfile ∘ vecNormSq) x v = _
    rw [h]
    simp only [smul_apply, sum_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hxn : vecEuclideanNorm x ≤ 1 ∨ deriv cutoffProfile (vecNormSq x) = 0 := by
    by_cases h : deriv cutoffProfile (vecNormSq x) = 0
    · exact Or.inr h
    · left
      have := (hzero _ h).2
      unfold vecEuclideanNorm
      rw [Real.sqrt_le_one]
      linarith
  rcases hxn with hxn | hxn
  · rw [hfd]
    calc |deriv cutoffProfile (vecNormSq x) * (2 * vecDot x v)|
        = |deriv cutoffProfile (vecNormSq x)| * (2 * |vecDot x v|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ L * (2 * (vecEuclideanNorm x * vecEuclideanNorm v)) := by
          apply mul_le_mul (hbound _) _ (by positivity) hL0
          exact mul_le_mul_of_nonneg_left (abs_vecDot_le_vecEuclideanNorm_mul x v) (by norm_num)
      _ ≤ L * (2 * (1 * vecEuclideanNorm v)) := by
          apply mul_le_mul_of_nonneg_left _ hL0
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hxn (vecEuclideanNorm_nonneg v)
      _ = 2 * L * vecEuclideanNorm v := by ring
  · rw [hfd, hxn, zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (vecEuclideanNorm_nonneg v)

/-- **Weighted Poincaré inequality for the explicit cutoff**: with `ρ = ζ²` and
`m = ∫ u ζ² / ∫ ζ²` over `B₁`,
`∫_{B₁} |u - m|² ζ² ≤ C(d) ∫_{B₁} |∇u|² ζ²`. -/
theorem weightedPoincare_radialCutoff {d : ℕ} {U : Set (Vec d)}
    (hU : euclideanBall (0 : Vec d) 1 ⊆ U) (u : H1Function U) :
    ∫ x in euclideanBall (0 : Vec d) 1,
        (u x - (∫ y in euclideanBall (0 : Vec d) 1, u y * radialCutoff d y ^ 2) /
          (∫ y in euclideanBall (0 : Vec d) 1, radialCutoff d y ^ 2)) ^ 2 *
            radialCutoff d x ^ 2 ≤
      weightedPoincareConst d *
        ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x) * radialCutoff d x ^ 2 :=
  weightedPoincare (ρ := fun x => radialCutoff d x ^ 2)
    (fun _ => sq_nonneg _)
    (fun x => pow_le_one₀ (radialCutoff_nonneg x) (radialCutoff_le_one x))
    (radialCutoff_sq_isRadialLevelWeight d) hU u

end PDE.Parabolic.WeakHarnack
