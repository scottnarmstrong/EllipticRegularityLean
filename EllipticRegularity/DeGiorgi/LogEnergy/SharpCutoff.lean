module

public import EllipticRegularity.DeGiorgi.LogEnergy.Profile
public import PDEFoundation.Sobolev.Cutoff.Ball
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Radial smooth cutoffs with a sharp gradient bound

For `0 < r < s₁ < s` and `0 < ε ≤ 1/4` there is a smooth cutoff equal to one on
`B_r(y)`, topologically supported in `B_s(y)`, with Euclidean gradient at most
`(1 - 2ε)⁻¹ / (s₁ - r)`.  Letting `ε → 0` and `s₁ → s` recovers the Lipschitz constant
`1 / (s - r)`.
-/

@[expose] public section

namespace PDE.DGNMLogEnergy

open Set Filter Topology

private theorem fderiv_coord_sub_const_apply_basisVec' {d : ℕ}
    (i j : Fin d) (c x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i - c i) x) (basisVec j) =
      if j = i then 1 else 0 := by
  rw [fderiv_sub_const]
  change
    (fderiv ℝ (⇑(ContinuousLinearMap.proj (R := ℝ) i)) x)
        (basisVec j) =
      _
  rw [ContinuousLinearMap.fderiv]
  simp [basisVec_apply, eq_comm]

private theorem fderiv_coord_sub_const_sq_apply_basisVec' {d : ℕ}
    (i j : Fin d) (c x : Vec d) :
    (fderiv ℝ (fun y : Vec d => (y i - c i) ^ 2) x)
        (basisVec j) =
      2 * (x i - c i) * (if j = i then 1 else 0) := by
  rw [fderiv_fun_pow]
  · simp [fderiv_coord_sub_const_apply_basisVec', pow_one,
      smul_eq_mul]
  · fun_prop

/-- The coordinate gradient of the squared Euclidean distance. -/
theorem classicalGradient_euclideanSqDist {d : ℕ} (x₀ x : Vec d) :
    classicalGradient (fun y : Vec d => euclideanSqDist y x₀) x = (2 : ℝ) • (x - x₀) := by
  have hfun :
      (fun y : Vec d => euclideanSqDist y x₀) =
        fun y : Vec d => ∑ i : Fin d, (y i - x₀ i) ^ 2 := by
    funext y
    simp only [euclideanSqDist, vecNormSq_eq_sum_sq, Pi.sub_apply]
  funext j
  rw [classicalGradient_apply, hfun, fderiv_fun_sum]
  · simp [fderiv_coord_sub_const_sq_apply_basisVec']
  · intro i _hi
    fun_prop

/-- The radial profile `ρ ↦ χ_ε((√ρ - r) / L)`. -/
noncomputable def radialProfile (ε r L ρ : ℝ) : ℝ :=
  sharpProfile ε ((Real.sqrt ρ - r) / L)

theorem radialProfile_eq_one {ε r L ρ : ℝ} (hε : 0 < ε) (hr : 0 < r) (hL : 0 < L)
    (hρ : ρ < r ^ 2) : radialProfile ε r L ρ = 1 := by
  unfold radialProfile
  apply sharpProfile_eq_one hε
  have : Real.sqrt ρ < r := (Real.sqrt_lt' hr).mpr hρ
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le

theorem radialProfile_eq_zero {ε r L s₁ ρ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hL : 0 < L)
    (hs : s₁ = r + L) (hs₁ : 0 ≤ s₁) (hρ : s₁ ^ 2 < ρ) : radialProfile ε r L ρ = 0 := by
  unfold radialProfile
  apply sharpProfile_eq_zero hε hε4
  have : s₁ < Real.sqrt ρ := (Real.lt_sqrt hs₁).mpr hρ
  rw [le_div_iff₀ hL]
  linarith

theorem radialProfile_contDiff {ε r L : ℝ} (hε : 0 < ε) (hr : 0 < r) (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (radialProfile ε r L) := by
  rw [contDiff_iff_contDiffAt]
  intro ρ
  by_cases hρ : ρ < r ^ 2
  · have h : radialProfile ε r L =ᶠ[𝓝 ρ] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hρ) fun t ht => radialProfile_eq_one hε hr hL ht
    exact (contDiffAt_const).congr_of_eventuallyEq h
  · have hpos : ρ ≠ 0 := by
      have : 0 < r ^ 2 := by positivity
      intro h; apply hρ; rw [h]; exact this
    have hs : ContDiffAt ℝ (⊤ : ℕ∞) Real.sqrt ρ := Real.contDiffAt_sqrt hpos
    exact (sharpProfile_contDiff ε).contDiffAt.comp ρ
      (((hs.sub contDiffAt_const).div_const L))

theorem radialProfile_deriv_bound {ε r L : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hr : 0 < r)
    (hL : 0 < L) (ρ : ℝ) :
    |deriv (radialProfile ε r L) ρ| * (2 * Real.sqrt ρ) ≤ (1 - 2 * ε)⁻¹ / L := by
  have hK : 0 ≤ (1 - 2 * ε)⁻¹ / L := by
    apply div_nonneg _ hL.le
    apply inv_nonneg.mpr; linarith
  by_cases hρ : ρ < r ^ 2
  · have h : radialProfile ε r L =ᶠ[𝓝 ρ] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hρ) fun t ht => radialProfile_eq_one hε hr hL ht
    rw [h.deriv_eq]
    simpa using hK
  · have hrpos : 0 < r ^ 2 := by positivity
    have hρpos : 0 < ρ := lt_of_lt_of_le hrpos (not_lt.mp hρ)
    have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρpos
    have hin : HasDerivAt (fun t => (Real.sqrt t - r) / L) ((1 / (2 * Real.sqrt ρ)) / L) ρ :=
      ((Real.hasDerivAt_sqrt hρpos.ne').sub_const r).div_const L
    have hout : HasDerivAt (sharpProfile ε) (deriv (sharpProfile ε) ((Real.sqrt ρ - r) / L))
        ((Real.sqrt ρ - r) / L) :=
      ((sharpProfile_contDiff ε).differentiable (by simp) _).hasDerivAt
    have hcomp := hout.comp ρ hin
    have hd : deriv (radialProfile ε r L) ρ =
        deriv (sharpProfile ε) ((Real.sqrt ρ - r) / L) * ((1 / (2 * Real.sqrt ρ)) / L) :=
      hcomp.deriv
    rw [hd, abs_mul]
    have hb := abs_deriv_sharpProfile_le hε hε4 ((Real.sqrt ρ - r) / L)
    have hpos2 : (0 : ℝ) < 2 * Real.sqrt ρ := by positivity
    have habs : |(1 / (2 * Real.sqrt ρ)) / L| = (1 / (2 * Real.sqrt ρ)) / L :=
      abs_of_pos (by positivity)
    rw [habs]
    calc |deriv (sharpProfile ε) ((Real.sqrt ρ - r) / L)| * ((1 / (2 * Real.sqrt ρ)) / L) *
          (2 * Real.sqrt ρ)
        = |deriv (sharpProfile ε) ((Real.sqrt ρ - r) / L)| / L := by
          field_simp
      _ ≤ (1 - 2 * ε)⁻¹ / L := div_le_div_of_nonneg_right hb hL.le

/-- The sharp radial cutoff: equal to `1` on `B_r(y)`, topologically supported in
`closedBall y s₁ ⊆ B_s(y)`, with Euclidean gradient at most `(1 - 2ε)⁻¹ / (s₁ - r)`. -/
noncomputable def sharpBallCutoff {d : ℕ} (y : Vec d) {r s₁ s ε : ℝ} (hr : 0 < r)
    (hrs₁ : r < s₁) (hs₁s : s₁ < s) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    QuantitativeSmoothCutoff (euclideanBall y r) (euclideanBall y s)
      ((1 - 2 * ε)⁻¹ / (s₁ - r)) where
  toFun x := radialProfile ε r (s₁ - r) (euclideanSqDist x y)
  smooth := (radialProfile_contDiff hε hr (sub_pos.mpr hrs₁)).comp
    (contDiff_euclideanSqDist_left y)
  hasCompactSupport := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall y (le_of_lt (hr.trans hrs₁))) ?_
    intro x hx
    by_contra hnot
    apply hx
    have hnot' : s₁ ^ 2 < euclideanSqDist x y := not_le.mp hnot
    exact radialProfile_eq_zero hε hε4 (sub_pos.mpr hrs₁) (by ring)
      (le_of_lt (hr.trans hrs₁)) hnot'
  tsupport_subset := by
    have hs₁ : 0 ≤ s₁ := le_of_lt (hr.trans hrs₁)
    have hsub : Function.support (fun x => radialProfile ε r (s₁ - r) (euclideanSqDist x y)) ⊆
        euclideanClosedBall y s₁ := by
      intro x hx
      by_contra hnot
      apply hx
      have hnot' : s₁ ^ 2 < euclideanSqDist x y := not_le.mp hnot
      exact radialProfile_eq_zero hε hε4 (sub_pos.mpr hrs₁) (by ring) hs₁ hnot'
    exact (closure_minimal hsub (isClosed_euclideanClosedBall y s₁)).trans
      (euclideanClosedBall_subset_euclideanBall hs₁ hs₁s)
  nonneg x := (sharpProfile_mem hε hε4 _).1
  le_one x := (sharpProfile_mem hε hε4 _).2
  eq_one_on_inner x hx := radialProfile_eq_one hε hr (sub_pos.mpr hrs₁) hx
  gradient_bound x := by
    have hL : 0 < s₁ - r := sub_pos.mpr hrs₁
    have hf := ((radialProfile_contDiff hε hr hL).differentiable (by simp)
      (euclideanSqDist x y))
    have hq : DifferentiableAt ℝ (fun z : Vec d => euclideanSqDist z y) x :=
      ((contDiff_euclideanSqDist_left y).differentiable (by simp)) x
    have hgrad : classicalGradient
        (fun x => radialProfile ε r (s₁ - r) (euclideanSqDist x y)) x =
        deriv (radialProfile ε r (s₁ - r)) (euclideanSqDist x y) •
          classicalGradient (fun z : Vec d => euclideanSqDist z y) x := by
      funext i
      change (fderiv ℝ (fun z => radialProfile ε r (s₁ - r) (euclideanSqDist z y)) x)
        (basisVec i) = _
      rw [fderiv_fun_comp x hf hq]
      simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul,
        Pi.smul_apply, smul_eq_mul, classicalGradient_apply]
    rw [hgrad, classicalGradient_euclideanSqDist, smul_smul, vecEuclideanNorm_smul]
    have hn : vecEuclideanNorm (x - y) = Real.sqrt (euclideanSqDist x y) := rfl
    have hb := radialProfile_deriv_bound hε hε4 hr hL (euclideanSqDist x y)
    rw [hn, abs_mul, abs_two]
    linarith

end PDE.DGNMLogEnergy
