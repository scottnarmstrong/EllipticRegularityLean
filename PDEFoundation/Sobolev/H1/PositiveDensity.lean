module

public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.H1.LevelSets
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Positivity-preserving density in `H¹₀`

This file strengthens an explicit supported smooth approximation of a
nonnegative `H¹` representative to one whose smooth approximants are
pointwise nonnegative.  The construction takes a subsequence converging
almost everywhere and applies the one-sided smooth positive-part
regularizer at a vanishing scale.

The gradient argument uses the exact level-set fact that the selected weak
gradient vanishes almost everywhere on `{u = 0}`.  Thus positivity is gained
without hiding a truncation or density theorem in an assumption.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- A nonnegative `H¹` representative with an explicit supported smooth
approximation admits another such approximation whose members are
pointwise nonnegative.

The conclusion is certificate-level, so every downstream use retains the
actual smooth functions, their support, and both `L²` convergence fields. -/
theorem exists_nonnegative_supportedSmoothApproximation
    (hU : IsOpenBoundedConvexDomain U)
    (happrox : u.SupportedSmoothApproximation)
    (hu : ∀ᵐ x ∂(volumeOn U), 0 ≤ u.toFun x) :
    ∃ hpositive : u.SupportedSmoothApproximation,
      ∀ n x, 0 ≤ hpositive.approx n x := by
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδPos : ∀ n, 0 < δ n := by
    intro n
    positivity
  have hδLeOne : ∀ n, δ n ≤ 1 := by
    intro n
    dsimp only [δ]
    rw [div_le_one (by positivity)]
    norm_num
  have hδTendsto : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have happroxMeas :
      ∀ n,
        AEStronglyMeasurable (happrox.approx n) (volumeOn U) := by
    intro n
    exact
      (happrox.toWeakTestFunction n).memLp_toFun
        (2 : ℝ≥0∞) |>.aestronglyMeasurable
  obtain ⟨σ, hσStrictMono, hσAeRaw⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
     
      happrox.tendsto_value).exists_seq_tendsto_ae
  have hσAe :
      ∀ᵐ x ∂(volumeOn U),
        Tendsto
          (fun i => happrox.approx (σ i) x)
          atTop (𝓝 (u.toFun x)) := by
    simpa only [H1Function.toW1pFunction_toFun] using hσAeRaw
  let positiveApprox : ℕ → Vec d → ℝ :=
    fun n x =>
      smoothPositivePartApprox 0 (δ n)
        (happrox.approx (σ n) x)
  have hpositiveSmooth :
      ∀ n, ContDiff ℝ (⊤ : ℕ∞) (positiveApprox n) := by
    intro n
    exact
      (smoothPositivePartApprox_contDiff 0 (δ n)).comp
        (happrox.approx_smooth (σ n))
  have hpositiveCompact :
      ∀ n, HasCompactSupport (positiveApprox n) := by
    intro n
    have h := (happrox.approx_hasCompactSupport (σ n)).comp_left
      (g := smoothPositivePartApprox 0 (δ n))
      (smoothPositivePartApprox_eq_zero_of_le (hδPos n) le_rfl)
    exact h
  have hpositiveSupport :
      ∀ n, tsupport (positiveApprox n) ⊆ U := by
    intro n
    refine
      (closure_mono
        (Function.support_comp_subset
          (smoothPositivePartApprox_eq_zero_of_le
            (hδPos n) le_rfl)
          (happrox.approx (σ n)))).trans ?_
    exact happrox.approx_tsupport_subset (σ n)
  have hpositiveNonnegative :
      ∀ n x, 0 ≤ positiveApprox n x := by
    intro n x
    exact smoothPositivePartApprox_nonneg
      (hδPos n) (happrox.approx (σ n) x)
  let valueRegularizationError : ℕ → Vec d → ℝ :=
    fun n x =>
      positiveApprox n x -
        max (happrox.approx (σ n) x) 0
  have hvalueRegularizationErrorMeas :
      ∀ n,
        AEStronglyMeasurable
          (valueRegularizationError n) (volumeOn U) := by
    intro n
    exact
      (hpositiveSmooth n).continuous.aestronglyMeasurable.sub
        (((happrox.approx_smooth (σ n)).continuous.max
          continuous_const).aestronglyMeasurable)
  have hvalueRegularizationErrorBound :
      ∀ n, ∀ᵐ x ∂(volumeOn U),
        ‖valueRegularizationError n x‖ ≤
          ‖(2 : ℝ)‖ := by
    intro n
    filter_upwards with x
    calc
      ‖valueRegularizationError n x‖ =
          |smoothPositivePartApprox 0 (δ n)
              (happrox.approx (σ n) x) -
            max (happrox.approx (σ n) x) 0| := by
        simp only [valueRegularizationError, positiveApprox,
          Real.norm_eq_abs]
      _ ≤ 2 * δ n := by
        simpa only [sub_zero] using
          abs_smoothPositivePartApprox_sub_le
            (c := 0) (hδPos n) (happrox.approx (σ n) x)
      _ ≤ ‖(2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
        linarith [hδLeOne n]
  have hvalueRegularizationErrorAe :
      ∀ᵐ x ∂(volumeOn U),
        Tendsto
          (fun n => valueRegularizationError n x)
          atTop (𝓝 0) := by
    filter_upwards with x
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have htwo :
        Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδTendsto.const_mul (2 : ℝ)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) htwo
    rw [Real.norm_eq_abs]
    simpa only [valueRegularizationError, positiveApprox,
      sub_zero] using
      abs_smoothPositivePartApprox_sub_le
        (c := 0) (hδPos n) (happrox.approx (σ n) x)
  have hvalueRegularizationErrorTendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (valueRegularizationError n)
            (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    have hraw :=
      tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
        (μ := volumeOn U) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num)
        hvalueRegularizationErrorMeas
        (MeasureTheory.MemLp.zero :
          MemLp (0 : Vec d → ℝ) (2 : ℝ≥0∞) (volumeOn U))
        (memLp_const (2 : ℝ))
        hvalueRegularizationErrorBound
        hvalueRegularizationErrorAe
    simpa only [Pi.sub_apply, sub_zero] using hraw
  let valuePositivePartError : ℕ → Vec d → ℝ :=
    fun n x =>
      max (happrox.approx (σ n) x) 0 - u.toFun x
  have hvaluePositivePartErrorMeas :
      ∀ n,
        AEStronglyMeasurable
          (valuePositivePartError n) (volumeOn U) := by
    intro n
    exact
      (((happrox.approx_smooth (σ n)).continuous.max
        continuous_const).aestronglyMeasurable).sub
        u.memL2.aestronglyMeasurable
  have hvaluePositivePartErrorBound :
      ∀ n,
        eLpNorm
            (valuePositivePartError n)
            (2 : ℝ≥0∞) (volumeOn U) ≤
          eLpNorm
            (fun x =>
              happrox.approx (σ n) x - u.toFun x)
            (2 : ℝ≥0∞) (volumeOn U) := by
    intro n
    apply eLpNorm_mono_ae (hvaluePositivePartErrorMeas n)
    filter_upwards [hu] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have huMax : max (u.toFun x) 0 = u.toFun x :=
      max_eq_left hx
    calc
      |valuePositivePartError n x| =
          |max (happrox.approx (σ n) x) 0 -
            max (u.toFun x) 0| := by
        rw [huMax]
      _ ≤ |happrox.approx (σ n) x - u.toFun x| :=
        abs_max_sub_max_le_abs
          (happrox.approx (σ n) x) (u.toFun x) 0
  have hvaluePositivePartErrorTendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (valuePositivePartError n)
            (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (happrox.tendsto_value.comp
          hσStrictMono.tendsto_atTop)
        (fun _ => zero_le)
        hvaluePositivePartErrorBound
  have hvalueTendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x => positiveApprox n x - u.toFun x)
            (2 : ℝ≥0∞) (volumeOn U))
        atTop (𝓝 0) := by
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm
                (valueRegularizationError n)
                (2 : ℝ≥0∞) (volumeOn U) +
              eLpNorm
                (valuePositivePartError n)
                (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [zero_add] using
        hvalueRegularizationErrorTendsto.add
          hvaluePositivePartErrorTendsto
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hsum
        (fun _ => zero_le)
        (fun n => by
          have hdecomp :
              (fun x => positiveApprox n x - u.toFun x) =
                valueRegularizationError n +
                  valuePositivePartError n := by
            funext x
            simp only [valueRegularizationError,
              valuePositivePartError, Pi.add_apply]
            ring
          rw [hdecomp]
          exact
            eLpNorm_add_le (by norm_num))
  have hgradZero :
      ∀ᵐ x ∂(volumeOn U),
        u.toFun x = 0 → u.grad x = 0 :=
    u.grad_ae_zero_on_level_set hU 0
  have hgradTendsto :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x =>
                (fderiv ℝ (positiveApprox n) x) (basisVec i) -
                  u.grad x i)
              (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
    intro i
    let first : ℕ → Vec d → ℝ :=
      fun n x =>
        smoothPositivePartStep 0 (δ n)
            (happrox.approx (σ n) x) *
          ((fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
            u.grad x i)
    let second : ℕ → Vec d → ℝ :=
      fun n x =>
        (smoothPositivePartStep 0 (δ n)
              (happrox.approx (σ n) x) - 1) *
          u.grad x i
    have hfirstMeas :
        ∀ n,
          AEStronglyMeasurable (first n) (volumeOn U) := by
      intro n
      exact
        ((smoothPositivePartStep_continuous 0 (δ n))
          |>.comp_aestronglyMeasurable
            (happroxMeas (σ n))).mul
          (((happrox.toWeakTestFunction (σ n)).memLp_partialDeriv
              i (2 : ℝ≥0∞)).aestronglyMeasurable.sub
            (u.grad_memL2 i).aestronglyMeasurable)
    have hfirstBound :
        ∀ n,
          eLpNorm (first n) (2 : ℝ≥0∞) (volumeOn U) ≤
            eLpNorm
              (fun x =>
                (fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
                  u.grad x i)
              (2 : ℝ≥0∞) (volumeOn U) := by
      intro n
      apply eLpNorm_mono_ae (hfirstMeas n)
      filter_upwards with x
      simp only [first, norm_mul, Real.norm_eq_abs]
      calc
        |smoothPositivePartStep 0 (δ n)
            (happrox.approx (σ n) x)| *
              ‖(fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
                u.grad x i‖ ≤
            1 *
              ‖(fderiv ℝ (happrox.approx (σ n)) x) (basisVec i) -
                u.grad x i‖ :=
          mul_le_mul_of_nonneg_right
            (abs_smoothPositivePartStep_le_one
              0 (δ n) (happrox.approx (σ n) x))
            (norm_nonneg _)
        _ = _ := one_mul _
    have hfirstTendsto :
        Tendsto
          (fun n =>
            eLpNorm (first n) (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (happrox.tendsto_grad i |>.comp
          hσStrictMono.tendsto_atTop)
        (fun _ => zero_le) hfirstBound
    have hsecondMeas :
        ∀ n,
          AEStronglyMeasurable (second n) (volumeOn U) := by
      intro n
      exact
        (((smoothPositivePartStep_continuous 0 (δ n))
          |>.comp_aestronglyMeasurable
            (happroxMeas (σ n))).sub
          aestronglyMeasurable_const).mul
          (u.grad_memL2 i).aestronglyMeasurable
    have hsecondBound :
        ∀ n, ∀ᵐ x ∂(volumeOn U),
          ‖second n x‖ ≤ ‖u.grad x i‖ := by
      intro n
      filter_upwards with x
      have hstepNonneg :
          0 ≤ smoothPositivePartStep 0 (δ n)
            (happrox.approx (σ n) x) :=
        smoothPositivePartStep_nonneg _ _ _
      have hstepLe :
          smoothPositivePartStep 0 (δ n)
              (happrox.approx (σ n) x) ≤ 1 :=
        smoothPositivePartStep_le_one _ _ _
      have hstepDiff :
          |smoothPositivePartStep 0 (δ n)
              (happrox.approx (σ n) x) - 1| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hstepLe)]
        linarith
      simp only [second, norm_mul, Real.norm_eq_abs]
      calc
        |smoothPositivePartStep 0 (δ n)
            (happrox.approx (σ n) x) - 1| *
              |u.grad x i| ≤
            1 * ‖u.grad x i‖ :=
          mul_le_mul_of_nonneg_right hstepDiff
            (abs_nonneg _)
        _ = _ := one_mul _
    have hsecondAe :
        ∀ᵐ x ∂(volumeOn U),
          Tendsto (fun n => second n x) atTop (𝓝 0) := by
      filter_upwards [hσAe, hu, hgradZero] with x hx hux hzero
      by_cases hpos : 0 < u.toFun x
      · have happ :
            ∀ᶠ n in atTop,
              u.toFun x / 2 <
                happrox.approx (σ n) x :=
          (tendsto_order.1 hx).1 _ (by linarith)
        have hscale :
            ∀ᶠ n in atTop,
              δ n < u.toFun x / 4 :=
          (tendsto_order.1 hδTendsto).2 _ (by linarith)
        have heventually :
            ∀ᶠ n in atTop, second n x = 0 := by
          filter_upwards [happ, hscale] with n hn hδn
          have hstep :
              smoothPositivePartStep 0 (δ n)
                  (happrox.approx (σ n) x) = 1 :=
            smoothPositivePartStep_eq_one
              (hδPos n) (by linarith)
          simp only [second, hstep, sub_self, zero_mul]
        exact
          Tendsto.congr'
            (heventually.mono fun _ hn => hn.symm)
            tendsto_const_nhds
      · have huZero : u.toFun x = 0 :=
          le_antisymm (not_lt.mp hpos) hux
        have hgradCoord : u.grad x i = 0 := by
          rw [hzero huZero]
          rfl
        simp only [second, hgradCoord, mul_zero]
        exact tendsto_const_nhds
    have hsecondRaw :=
      tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
        (μ := volumeOn U) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num)
        hsecondMeas
        (MeasureTheory.MemLp.zero :
          MemLp (0 : Vec d → ℝ) (2 : ℝ≥0∞) (volumeOn U))
        (u.grad_memL2 i)
        hsecondBound hsecondAe
    have hsecondTendsto :
        Tendsto
          (fun n =>
            eLpNorm (second n) (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [Pi.sub_apply, sub_zero] using hsecondRaw
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm (first n) (2 : ℝ≥0∞) (volumeOn U) +
              eLpNorm (second n) (2 : ℝ≥0∞) (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [zero_add] using
        hfirstTendsto.add hsecondTendsto
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hsum
        (fun _ => zero_le)
        (fun n => by
          have hdecomp :
              (fun x =>
                (fderiv ℝ (positiveApprox n) x) (basisVec i) -
                  u.grad x i) =
                first n + second n := by
            funext x
            have hchain :
                (fderiv ℝ (positiveApprox n) x) (basisVec i) =
                  smoothPositivePartStep 0 (δ n)
                      (happrox.approx (σ n) x) *
                    (fderiv ℝ (happrox.approx (σ n)) x)
                      (basisVec i) := by
              simpa only [positiveApprox,
                deriv_smoothPositivePartApprox] using
                fderiv_comp_basisVec
                  ((smoothPositivePartApprox_contDiff
                    0 (δ n)).differentiable
                      (by simp)).differentiableAt
                  ((happrox.approx_smooth (σ n)).differentiable
                    (by simp)).differentiableAt
            rw [hchain]
            simp only [first, second, Pi.add_apply]
            ring
          rw [hdecomp]
          exact
            eLpNorm_add_le (by norm_num))
  refine ⟨?_, ?_⟩
  · exact
      { approx := positiveApprox
        approx_smooth := hpositiveSmooth
        approx_hasCompactSupport := hpositiveCompact
        approx_tsupport_subset := hpositiveSupport
        tendsto_value := hvalueTendsto
        tendsto_grad := hgradTendsto }
  · exact hpositiveNonnegative

end H1Function

end PDE
