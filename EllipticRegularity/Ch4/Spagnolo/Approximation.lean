module

public import EllipticRegularity.Ch4.Spagnolo.Setup
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Measure.LpPower

/-!
# Smooth approximation on the unit disc

Every `u ∈ H¹(B₁)` is the `H¹(B₁)` limit of globally smooth functions (the
repository's convex approximation). We record the convergence in the squared
form used by the Piccinini--Spagnolo argument: for a continuous nonnegative
radial weight `k`, `∫_{B₁} k(|x|²) (u - v_n)² → 0` and
`∫_{B₁} k(|x|²) (x⊥ · ∇v_n - x⊥ · ∇u)² → 0`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set Filter
open scoped Topology

private theorem closedBall_half_subset :
    Metric.closedBall (0 : Vec 2) (1 / 2) ⊆ euclideanBall (0 : Vec 2) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)] at hx
  refine mem_ball_one_iff.2 ?_
  have h0 : |x 0| ≤ 1 / 2 := by simpa [Real.norm_eq_abs] using hx 0
  have h1 : |x 1| ≤ 1 / 2 := by simpa [Real.norm_eq_abs] using hx 1
  have h0' : x 0 ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs (x 0), abs_nonneg (x 0)]
  have h1' : x 1 ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs (x 1), abs_nonneg (x 1)]
  have : vecNormSq x = x 0 ^ 2 + x 1 ^ 2 := by
    simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
  rw [this]
  linarith

private theorem tendsto_integral_sq_of_tendsto_eLpNorm {f : ℕ → Vec 2 → ℝ}
    (hf : ∀ n, MemL2On (euclideanBall (0 : Vec 2) 1) (f n))
    (h : Tendsto (fun n => eLpNorm (f n) 2 (volumeOn (euclideanBall (0 : Vec 2) 1)))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1, f n x ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => (eLpNorm (f n) 2
      (volumeOn (euclideanBall (0 : Vec 2) 1))).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa only [ENNReal.toReal_zero, Function.comp_def] using this
  have h2 := h1.pow 2
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun n => ?_
  exact toReal_eLpNorm_two_sq_eq_integral_sq (hf n)

/-- **Smooth approximation.** Globally smooth `v_n` with `v_n → u` and
`∇v_n → ∇u` in `L²(B₁)`, in squared-integral form. -/
theorem exists_smooth_approximation (u : H1Function (euclideanBall (0 : Vec 2) 1)) :
    ∃ v : ℕ → Vec 2 → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n)) ∧
      Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1, (v n x - u x) ^ 2)
        atTop (𝓝 0) ∧
      ∀ i : Fin 2, Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1,
        (classicalGradient (v n) x i - u.grad x i) ^ 2) atTop (𝓝 0) := by
  have hU := isOpenBoundedConvexDomain_euclideanBall (0 : Vec 2) one_pos
  have hp : (1 : ENNReal) ≤ 2 := by norm_num
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  let w : ℕ → W1pFunction (euclideanBall (0 : Vec 2) 1) 2 := fun n =>
    W1pFunction.convexApproxSmoothW1p hU hp u.toW1pFunction 0 hr n
  refine ⟨fun n => (w n).toFun, fun n =>
    W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU hp u.toW1pFunction 0 hr n, ?_, ?_⟩
  · refine tendsto_integral_sq_of_tendsto_eLpNorm (fun n => (w n).memLp.sub u.memL2) ?_
    exact W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp (by norm_num)
      u.toW1pFunction closedBall_half_subset hr
  · intro i
    refine tendsto_integral_sq_of_tendsto_eLpNorm (fun n => ((w n).gradMemLp i).sub
      (u.grad_memL2 i)) ?_
    exact W1pFunction.tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub hU hp
      (by norm_num) u.toW1pFunction closedBall_half_subset hr i

/-- Weighted convergence of values: `∫_{B₁} k(|x|²) (u - v_n)² → 0`. -/
theorem tendsto_weighted_sq_sub {u : Vec 2 → ℝ} {v : ℕ → Vec 2 → ℝ}
    (hu : MemL2On (euclideanBall (0 : Vec 2) 1) u) (hv : ∀ n, Continuous (v n))
    (hconv : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1, (v n x - u x) ^ 2)
      atTop (𝓝 0))
    {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ t, 0 ≤ k t) :
    Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1,
      k (vecNormSq x) * (u x - v n x) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous (hk.comp continuous_vecNormSq)
  have hsq : ∀ n, IntegrableOn (fun x => (v n x - u x) ^ 2) (euclideanBall (0 : Vec 2) 1) :=
    fun n => MemLp.integrable_sq ((memL2On_of_continuous (hv n)).sub hu)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) (by simpa using hconv.const_mul C)
  · refine setIntegral_nonneg (measurableSet_euclideanBall _ _) fun x _ => ?_
    exact mul_nonneg (hk0 _) (sq_nonneg _)
  · rw [← integral_const_mul]
    refine setIntegral_mono_on ?_ ((hsq n).const_mul C) (measurableSet_euclideanBall _ _)
      fun x hx => ?_
    · have := integrableOn_continuous_mul (hk.comp continuous_vecNormSq) (hsq n)
      refine this.congr_fun (fun x _ => ?_) (measurableSet_euclideanBall _ _)
      simp only [Function.comp_apply]; ring
    · have hkx : k (vecNormSq x) ≤ C := (le_abs_self _).trans (hC x hx)
      have : (u x - v n x) ^ 2 = (v n x - u x) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hkx (sq_nonneg _)

/-- Weighted convergence of tangential derivatives:
`∫_{B₁} k(|x|²) (x⊥ · ∇v_n - x⊥ · ∇u)² → 0`. -/
theorem tendsto_weighted_sq_perpDot_sub {g : Vec 2 → Vec 2} {v : ℕ → Vec 2 → ℝ}
    (hg : MemVectorL2On (euclideanBall (0 : Vec 2) 1) g)
    (hv : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n))
    (hconv : ∀ i : Fin 2, Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1,
      (classicalGradient (v n) x i - g x i) ^ 2) atTop (𝓝 0))
    {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ t, 0 ≤ k t) :
    Tendsto (fun n => ∫ x in euclideanBall (0 : Vec 2) 1,
      k (vecNormSq x) * (perpDot x (classicalGradient (v n) x) - perpDot x (g x)) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous (hk.comp continuous_vecNormSq)
  have hgradc : ∀ n i, Continuous (fun x => classicalGradient (v n) x i) := fun n i =>
    ((hv n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hΔ : ∀ n i, MemL2On (euclideanBall (0 : Vec 2) 1)
      (fun x => classicalGradient (v n) x i - g x i) :=
    fun n i => (memL2On_of_continuous (hgradc n i)).sub (hg i)
  have hsq : ∀ n i, IntegrableOn (fun x => (classicalGradient (v n) x i - g x i) ^ 2)
      (euclideanBall (0 : Vec 2) 1) := fun n i => MemLp.integrable_sq (hΔ n i)
  have hbound := ((hconv 0).add (hconv 1)).const_mul (2 * C)
  rw [add_zero, mul_zero] at hbound
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hbound
  · refine setIntegral_nonneg (measurableSet_euclideanBall _ _) fun x _ => ?_
    exact mul_nonneg (hk0 _) (sq_nonneg _)
  · rw [← integral_add (hsq n 0) (hsq n 1), ← integral_const_mul]
    have hpt : ∀ x, perpDot x (classicalGradient (v n) x) - perpDot x (g x) =
        x 0 * (classicalGradient (v n) x 1 - g x 1) -
          x 1 * (classicalGradient (v n) x 0 - g x 0) := by
      intro x; simp only [perpDot]; ring
    simp only [hpt]
    have hperp : MemL2On (euclideanBall (0 : Vec 2) 1)
        (fun x => x 0 * (classicalGradient (v n) x 1 - g x 1) -
          x 1 * (classicalGradient (v n) x 0 - g x 0)) :=
      (memL2On_continuous_mul (continuous_apply 0) (hΔ n 1)).sub
        (memL2On_continuous_mul (continuous_apply 1) (hΔ n 0))
    refine setIntegral_mono_on
      (integrableOn_continuous_mul (hk.comp continuous_vecNormSq) (MemLp.integrable_sq hperp))
      (((hsq n 0).add (hsq n 1)).const_mul _) (measurableSet_euclideanBall _ _)
      fun x hx => ?_
    have hkx : k (vecNormSq x) ≤ C := (le_abs_self _).trans (hC x hx)
    have hx0 : x 0 ^ 2 ≤ 1 := by
      have := abs_apply_le_one_of_mem hx 0
      nlinarith [sq_abs (x 0), abs_nonneg (x 0)]
    have hx1 : x 1 ^ 2 ≤ 1 := by
      have := abs_apply_le_one_of_mem hx 1
      nlinarith [sq_abs (x 1), abs_nonneg (x 1)]
    set A := classicalGradient (v n) x 0 - g x 0
    set B := classicalGradient (v n) x 1 - g x 1
    have h1 : (x 0 * B - x 1 * A) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
      have h2 : (x 0 * B - x 1 * A) ^ 2 ≤ 2 * (x 0 ^ 2 * B ^ 2 + x 1 ^ 2 * A ^ 2) := by
        nlinarith [sq_nonneg (x 0 * B + x 1 * A)]
      have h3 : x 0 ^ 2 * B ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg B]
      have h4 : x 1 ^ 2 * A ^ 2 ≤ A ^ 2 := by nlinarith [sq_nonneg A]
      linarith
    calc k (vecNormSq x) * (x 0 * B - x 1 * A) ^ 2 ≤ C * (2 * (A ^ 2 + B ^ 2)) :=
          mul_le_mul hkx h1 (sq_nonneg _) hC0
      _ = 2 * C * (A ^ 2 + B ^ 2) := by ring

end PDE.Ch4Spagnolo
