module

public import PDEFoundation.Sobolev.Ch4.Lipschitz
public import PDEFoundation.Sobolev.WeakDerivative

/-!
# Weak gradient of a Lipschitz function

A Euclidean-Lipschitz function `η` on `Vec d` has, as weak partial derivative, its almost
everywhere classical derivative `x ↦ fderiv ℝ η x (basisVec i)` (Rademacher).  The proof passes
to the limit in the translation identity
`∫ η(x) (φ(x + h e) - φ(x)) / h = - ∫ ((η(x) - η(x - h e)) / h) φ(x)`
by dominated convergence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE.Ch4Infra

variable {d : ℕ}

/-- Directional slopes converge to the derivative at a point of differentiability. -/
theorem tendsto_slope_direction {f : Vec d → ℝ} {x : Vec d} (hx : DifferentiableAt ℝ f x)
    (e : Vec d) :
    Tendsto (fun t : ℝ => (f (x + t • e) - f x) / t) (𝓝[≠] 0) (𝓝 (fderiv ℝ f x e)) := by
  have hγ : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hx' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • e) := by simpa using hx.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => f (x + t • e)) (fderiv ℝ f x e) 0 :=
    hx'.comp_hasDerivAt (0 : ℝ) hγ
  have := h1.tendsto_slope_zero
  refine this.congr fun t => ?_
  simp [div_eq_inv_mul]

theorem EucLip.hasWeakPartialDerivOn_univ {L : ℝ} {η : Vec d → ℝ} (hη : EucLip L η)
    (hL : 0 ≤ L) (i : Fin d) :
    HasWeakPartialDerivOn Set.univ i η (fun x => fderiv ℝ η x (basisVec i)) := by
  intro φ hφ hφc _
  simp only [Measure.restrict_univ]
  set e : Vec d := basisVec i with he
  have hηc : Continuous η := hη.continuous hL
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Kφ, hKφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  let hh : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos : ∀ n, 0 < hh n := fun n => by positivity
  have hle1 : ∀ n, hh n ≤ 1 := fun n => by
    simp only [hh]
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h0 : Tendsto hh atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h0' : Tendsto hh atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall fun n => (hpos n).ne'⟩
  have h0'' : Tendsto (fun n => -hh n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using h0.neg,
      Eventually.of_forall fun n => (neg_ne_zero.2 (hpos n).ne')⟩
  have hnorme : ‖e‖ = 1 := by simp [he, basisVec, Pi.norm_single]
  have hesq : vecEuclideanNorm e = 1 := vecEuclideanNorm_basisVec i
  set S : Set (Vec d) := Metric.cthickening 1 (tsupport φ) with hSdef
  have hS : IsCompact S := hφc.isCompact.cthickening
  obtain ⟨Mη, hMη⟩ := hS.exists_bound_of_continuousOn hηc.continuousOn
  set Q : ℕ → Vec d → ℝ := fun n x => (φ (x + hh n • e) - φ x) / hh n with hQ
  set R : ℕ → Vec d → ℝ := fun n x => (η x - η (x - hh n • e)) / hh n with hR
  -- the shifted functions are compactly supported
  have hshc : ∀ n, HasCompactSupport (fun x => φ (x + hh n • e)) := fun n =>
    hφc.comp_homeomorph (Homeomorph.addRight (hh n • e))
  -- support of the slope
  have hQS : ∀ n x, x ∉ S → Q n x = 0 := by
    intro n x hxS
    have h1 : φ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hxS (Metric.self_subset_cthickening _ hm)
    have h2 : φ (x + hh n • e) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      apply hxS
      refine Metric.mem_cthickening_of_dist_le x (x + hh n • e) 1 _ hm ?_
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hnorme, Real.norm_of_nonneg (hpos n).le]
      linarith [hle1 n]
    simp [hQ, h1, h2]
  have hQb : ∀ n x, |Q n x| ≤ Kφ := by
    intro n x
    have := hKφ.dist_le_mul (x + hh n • e) x
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, hnorme,
      Real.norm_of_nonneg (hpos n).le] at this
    simp only [hQ, abs_div, abs_of_pos (hpos n)]
    rw [div_le_iff₀ (hpos n)]
    simpa [mul_comm] using this
  -- first limit
  have T1 : Tendsto (fun n => ∫ x, η x * Q n x) atTop
      (𝓝 (∫ x, η x * fderiv ℝ φ x e)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => S.indicator (fun _ => Mη * Kφ) x) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (hηc.mul (((hφcont.comp (continuous_id.add continuous_const)).sub hφcont).div_const _)).aestronglyMeasurable
    · rw [integrable_indicator_iff hS.measurableSet]
      exact integrableOn_const hS.measure_lt_top.ne
    · refine Eventually.of_forall fun x => ?_
      by_cases hxS : x ∈ S
      · simp only [hxS, indicator_of_mem, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (by simpa using hMη x hxS) (hQb n x) (abs_nonneg _) ((abs_nonneg _).trans (by simpa using hMη x hxS))
      · simp [hxS, hQS n x hxS]
    · refine Eventually.of_forall fun x => ?_
      exact ((tendsto_slope_direction (hφd x) e).comp h0').const_mul (η x)
  -- second limit
  have T2 : Tendsto (fun n => ∫ x, -(R n x * φ x)) atTop
      (𝓝 (∫ x, -(fderiv ℝ η x e * φ x))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => L * |φ x|) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact (((hηc.sub (hηc.comp (continuous_sub_right _))).div_const _).mul hφcont).neg.aestronglyMeasurable
    · exact (hφcont.abs.integrable_of_hasCompactSupport hφc.abs).const_mul L
    · refine Eventually.of_forall fun x => ?_
      have h1 := hη x (x - hh n • e)
      rw [sub_sub_cancel, vecEuclideanNorm_smul, hesq, abs_of_pos (hpos n),
        mul_one] at h1
      have h2 : |R n x| ≤ L := by
        simp only [hR, abs_div, abs_of_pos (hpos n)]
        rw [div_le_iff₀ (hpos n)]; linarith
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    · filter_upwards [hη.ae_differentiableAt hL] with x hx
      have h1 := (tendsto_slope_direction hx e).comp h0''
      have h2 : Tendsto (fun n => R n x) atTop (𝓝 (fderiv ℝ η x e)) := by
        refine h1.congr fun n => ?_
        simp only [Function.comp, hR, neg_smul, sub_eq_add_neg]
        rw [div_neg, ← neg_div]; ring_nf
      exact (h2.mul_const (φ x)).neg
  -- the translation identity
  have hI1 : ∀ n, Integrable (fun x => η x * φ (x + hh n • e)) := fun n =>
    (hηc.mul (hφcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hshc n).mul_left
  have hI2 : Integrable (fun x => η x * φ x) :=
    (hηc.mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
  have hI3 : ∀ n, Integrable (fun x => η (x - hh n • e) * φ x) := fun n =>
    ((hηc.comp (continuous_id.sub continuous_const)).mul hφcont).integrable_of_hasCompactSupport
      hφc.mul_left
  have hshift : ∀ n, ∫ x, η x * φ (x + hh n • e) = ∫ x, η (x - hh n • e) * φ x := fun n => by
    have := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
      (fun x => η (x - hh n • e) * φ x) (hh n • e)
    simpa using this
  have hid : ∀ n, ∫ x, η x * Q n x = ∫ x, -(R n x * φ x) := fun n => by
    have e1 : ∫ x, η x * Q n x =
        ((∫ x, η x * φ (x + hh n • e)) - ∫ x, η x * φ x) / hh n := by
      rw [← integral_sub (hI1 n) hI2, ← integral_div]
      congr 1; funext x; simp only [hQ]; ring
    have e2 : ∫ x, -(R n x * φ x) =
        ((∫ x, η (x - hh n • e) * φ x) - ∫ x, η x * φ x) / hh n := by
      rw [← integral_sub (hI3 n) hI2, ← integral_div]
      congr 1; funext x; simp only [hR]; ring
    rw [e1, e2, hshift n]
  have hlim := tendsto_nhds_unique T1 (T2.congr fun n => (hid n).symm)
  rw [integral_neg] at hlim
  exact hlim

end PDE.Ch4Infra
