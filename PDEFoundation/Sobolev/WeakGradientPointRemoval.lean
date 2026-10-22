module

public import PDEFoundation.Measure.ExtendedHolderNorm
public import PDEFoundation.Measure.ShrinkingBallLp
public import PDEFoundation.Sobolev.Cutoff.PointRemovalEuclidean
public import PDEFoundation.Sobolev.WeakDerivative

/-! # The cutoff error at a removable point -/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The term containing the gradient of the canonical point-removal cutoff
vanishes against every weak test function.  This is the quantitative core of
removing a point from a weak-gradient identity in dimensions at least two. -/
theorem tendsto_lintegral_weakTestFunction_mul_pointRemovalGradient_zero
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (φ : WeakTestFunction U) (i : Fin d)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫⁻ x in U,
        ENNReal.ofReal |f x * φ x *
          classicalGradient (pointRemovalCutoff (ε n)) x i|)
      atTop (𝓝 0) := by
  let μ : Measure (Vec d) := volume.restrict U
  let B : ℕ → Set (Vec d) := fun n => euclideanBall 0 (2 * ε n)
  let g : ℕ → Vec d → ℝ := fun n => (B n).indicator f
  let h : ℕ → Vec d → ℝ := fun n x =>
    vecEuclideanNorm (classicalGradient (pointRemovalCutoff (ε n)) x)
  obtain ⟨C, hC⟩ := φ.contDiff.continuous.bounded_above_of_compact_support
    φ.hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  let K : ℝ≥0∞ := ENNReal.ofReal 32 *
    (ENNReal.ofReal ((2 : ℝ) ^ d) *
      volume (euclideanBall (0 : Vec d) 1)) ^ (1 / (2 : ℝ))
  have hg0 : Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (𝓝 0) := by
    simpa only [g, B, μ] using
      tendsto_eLpNorm_indicator_euclideanBall_zero
        (lt_of_lt_of_le (by norm_num) hd) hf ε hε hε0
  have hhCont (n : ℕ) : Continuous (h n) := by
    have hsmooth := canonicalBallCutoff_smooth (x₀ := (0 : Vec d))
      (hε n).le (by linarith [hε n] : ε n < 2 * ε n)
    exact continuous_vecEuclideanNorm.comp
      (PDE.ContDiff.continuous_classicalGradient (hsmooth.of_le (by simp)))
  have hhMeas (n : ℕ) : AEMeasurable (fun x => ‖h n x‖ₑ) μ :=
    (hhCont n).aestronglyMeasurable.enorm
  have hholder (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal |g n x| * ‖h n x‖ₑ ∂μ) ≤
        eLpNorm (g n) 2 μ * eLpNorm (h n) 2 μ := by
    have hm : AEStronglyMeasurable (g n) μ :=
      (hf.indicator (measurableSet_euclideanBall 0 (2 * ε n))).aestronglyMeasurable
    have hh := lintegral_abs_mul_le_eLpNorm_mul_conjugate μ (g n) hm
      (fun x => ‖h n x‖ₑ) (hhMeas n) (p := 2) (by norm_num)
    convert hh using 1
    norm_num [Real.conjExponent,
      eLpNorm_enorm (h n) (hhCont n).aestronglyMeasurable]
  have hhK (n : ℕ) : eLpNorm (h n) 2 μ ≤ K := by
    exact (eLpNorm_mono_measure (h n) Measure.restrict_le_self).trans
      (pointRemovalCutoff_euclideanGradient_eLpNorm_two_uniform
        hd (hε n) (hε1 n))
  have hbase : Tendsto
      (fun n => ∫⁻ x, ENNReal.ofReal |g n x| * ‖h n x‖ₑ ∂μ)
      atTop (𝓝 0) := by
    have hKtop : K ≠ ∞ := by
      dsimp [K]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (volume_euclideanBall_ne_top 0 (by positivity))))
    have hprod : Tendsto (fun n => eLpNorm (g n) 2 μ * K)
        atTop (nhds 0) := by
      simpa only [Function.comp_apply, zero_mul] using!
        (((ENNReal.continuous_mul_const hKtop).tendsto 0).comp hg0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hprod (by simp) ?_
    · filter_upwards with n
      exact (hholder n).trans (mul_le_mul_right (hhK n) _)
  have hweighted : Tendsto
      (fun n => ENNReal.ofReal C *
        ∫⁻ x, ENNReal.ofReal |g n x| * ‖h n x‖ₑ ∂μ)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using!
      (((ENNReal.continuous_const_mul (a := ENNReal.ofReal C)
        ENNReal.ofReal_ne_top).tendsto 0).comp hbase)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hweighted (by simp) ?_
  filter_upwards with n
  change (∫⁻ x, ENNReal.ofReal |f x * φ x *
    classicalGradient (pointRemovalCutoff (ε n)) x i| ∂μ) ≤ _
  let W : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal C *
    (ENNReal.ofReal |g n x| * ‖h n x‖ₑ)
  have hpoint (x : Vec d) :
      ENNReal.ofReal |f x * φ x *
        classicalGradient (pointRemovalCutoff (ε n)) x i| ≤ W x := by
    by_cases hx : x ∈ B n
    · have hcoord := abs_apply_le_vecEuclideanNorm
        (classicalGradient (pointRemovalCutoff (ε n)) x) i
      have hφ := hC x
      simp only [W, g, B, hx, indicator_of_mem, Real.enorm_eq_ofReal_abs,
        h] at hcoord ⊢
      rw [abs_mul, abs_mul]
      have hrle : |f x| * |φ x| *
          |classicalGradient (pointRemovalCutoff (ε n)) x i| ≤
          C * (|f x| * vecEuclideanNorm
            (classicalGradient (pointRemovalCutoff (ε n)) x)) := by
        calc
          _ ≤ |f x| * C *
              |classicalGradient (pointRemovalCutoff (ε n)) x i| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hφ)
                (abs_nonneg (f x))) (abs_nonneg _)
          _ ≤ |f x| * C * vecEuclideanNorm
              (classicalGradient (pointRemovalCutoff (ε n)) x) :=
            mul_le_mul_of_nonneg_left hcoord
              (mul_nonneg (abs_nonneg _) hC0)
          _ = _ := by ring
      simpa [ENNReal.ofReal_mul, hC0, abs_nonneg,
        abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
          ENNReal.ofReal_le_ofReal hrle
    · have hr : 2 * ε n ≤ vecEuclideanNorm x := by
        change x ∉ euclideanBall 0 (2 * ε n) at hx
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt
          (mul_pos (by norm_num) (hε n))] at hx
        simpa only [sub_zero] using not_lt.mp hx
      have hz := pointRemovalCutoff_gradient_zero (hε n) hr
      change ENNReal.ofReal |f x * φ x *
        classicalGradient (pointRemovalCutoff (ε n)) x i| ≤ W x
      rw [congrFun hz i]
      simp [W, g, B, hx]
  calc
    _ ≤ ∫⁻ x, W x ∂μ := lintegral_mono hpoint
    _ = _ := by
      simp only [W]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Bochner-integral form of the cutoff-gradient error estimate. -/
theorem tendsto_integral_weakTestFunction_mul_pointRemovalGradient_zero
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (φ : WeakTestFunction U) (i : Fin d)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hε0 : Tendsto ε atTop (nhds 0)) :
    Tendsto
      (fun n ↦ ∫ x in U,
        f x * φ x * classicalGradient (pointRemovalCutoff (ε n)) x i)
      atTop (nhds 0) := by
  let μ : Measure (Vec d) := volume.restrict U
  let L : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x in U,
    ENNReal.ofReal |f x * φ x *
      classicalGradient (pointRemovalCutoff (ε n)) x i|
  have hL : Tendsto L atTop (nhds 0) :=
    tendsto_lintegral_weakTestFunction_mul_pointRemovalGradient_zero
      hd hf φ i ε hε hε1 hε0
  have hLreal : Tendsto (fun n ↦ (L n).toReal) atTop (nhds 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_apply] using!
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · filter_upwards with n
    exact norm_nonneg _
  · filter_upwards with n
    change ‖∫ x, f x * φ x *
      classicalGradient (pointRemovalCutoff (ε n)) x i ∂μ‖ ≤ _
    simpa only [L, Real.norm_eq_abs] using
      (norm_integral_le_lintegral_norm (fun x ↦ f x * φ x *
        classicalGradient (pointRemovalCutoff (ε n)) x i) (μ := μ))
  · exact hLreal

end

end PDE
