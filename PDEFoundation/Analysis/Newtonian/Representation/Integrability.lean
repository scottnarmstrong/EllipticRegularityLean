module

public import PDEFoundation.Analysis.Newtonian.Representation.Mollifier

/-!
# Integrability and the `ε → 0` limit of the regularized kernel against test fields

For `h` continuous with compact support, `y ↦ E_i(x - y) h(y)` is integrable, and
`∫ regKernel ε (x - y) i * h y → ∫ newtonKernel (x - y) i * h y` as `ε → 0⁺` by dominated convergence.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PDE

namespace NewtonRepresentation

noncomputable section

variable {d : ℕ}

theorem exists_subset_euclideanBall_of_isCompact {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ euclideanBall (0 : Vec d) R := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun z : Vec d => vecEuclideanNorm z)
    continuous_vecEuclideanNorm.continuousOn
  have hM0 : 0 ≤ |M| := abs_nonneg M
  refine ⟨|M| + 1, by positivity, fun y hy => ?_⟩
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]
  have := hM y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg y)] at this
  have := le_abs_self M
  linarith [hM y hy, abs_of_nonneg (vecEuclideanNorm_nonneg y)]

theorem integrable_newtonKernel_apply_mul (hd : 0 < d) {h : Vec d → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) (i : Fin d) (x : Vec d) :
    Integrable (fun y => newtonKernel (x - y) i * h y) := by
  obtain ⟨R, hR, hKR⟩ := exists_subset_euclideanBall_of_isCompact hc
  set R' : ℝ := vecEuclideanNorm x + R with hR'
  have hR'pos : 0 < R' := by have := vecEuclideanNorm_nonneg x; positivity
  set Eloc : Vec d → ℝ :=
    (euclideanBall (0 : Vec d) R').indicator (fun z => newtonKernel z i) with hEloc
  have hEint : Integrable Eloc :=
    (integrable_indicator_iff (measurableSet_euclideanBall _ _)).2
      (integrableOn_euclideanBall_newtonKernel_apply hd i hR'pos)
  have h1 : Integrable (fun y => Eloc (x - y)) := (integrable_comp_sub_left Eloc x).2 hEint
  have h2 := h1.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hh hc
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ tsupport h
  · have hxy : x - y ∈ euclideanBall (0 : Vec d) R' := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR'pos, sub_zero]
      have hy' := hKR hy
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_zero] at hy'
      calc vecEuclideanNorm (x - y) ≤ vecEuclideanNorm x + vecEuclideanNorm (-y) := by
            have := vecEuclideanNorm_add_le x (-y)
            simpa [sub_eq_add_neg] using this
        _ = vecEuclideanNorm x + vecEuclideanNorm y := by rw [vecEuclideanNorm_neg]
        _ < R' := by linarith
    simp [hEloc, Set.indicator_of_mem hxy]
  · have : h y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]

theorem abs_regKernel_apply_le (hd : 0 < d) (ε : ℝ) (z : Vec d) (i : Fin d) :
    |regKernel ε z i| ≤ |newtonKernel z i| := by
  by_cases hz : z = 0
  · subst hz; simp [regKernel, newtonKernel]
  · rw [← regKernel_zero_eps]
    simp only [regKernel, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (regCoef_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regCoef_le hd ε hz) (abs_nonneg _)

theorem tendsto_integral_regKernel_apply_mul (hd : 0 < d) {h : Vec d → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) (i : Fin d) (x : Vec d) :
    Tendsto (fun ε : ℝ => ∫ y, regKernel ε (x - y) i * h y) (𝓝[>] 0)
      (𝓝 (∫ y, newtonKernel (x - y) i * h y)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => |newtonKernel (x - y) i * h y|) ?_ ?_
    (integrable_newtonKernel_apply_mul hd hh hc i x).abs ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : ε ≠ 0 := ne_of_gt hε
    have : Continuous (fun y : Vec d => regKernel ε (x - y) i * h y) :=
      ((contDiff_regKernel_apply hε' i).continuous.comp (by fun_prop)).mul hh
    exact this.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_regKernel_apply_le hd ε _ i) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 : Tendsto (fun ε : ℝ => regKernel ε (x - y)) (𝓝 0) (𝓝 (newtonKernel (x - y))) :=
      tendsto_regKernel _
    have h2 : Tendsto (fun ε : ℝ => regKernel ε (x - y) i) (𝓝 0) (𝓝 (newtonKernel (x - y) i)) :=
      (continuous_apply i).continuousAt.tendsto.comp h1
    exact (h2.mul_const _).mono_left nhdsWithin_le_nhds

end

end NewtonRepresentation

end PDE
