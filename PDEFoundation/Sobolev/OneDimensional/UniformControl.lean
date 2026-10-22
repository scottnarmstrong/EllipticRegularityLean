module

public import PDEFoundation.Sobolev.OneDimensional.Primitive
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform control on a scalar interval

This module records the quantitative one-dimensional estimate that upgrades
`L²` control of a smooth scalar function and its derivative to pointwise
control on a fixed nondegenerate interval.
-/

@[expose] public section

open scoped ENNReal Topology Interval

namespace PDE

open Filter MeasureTheory Set

noncomputable section

private theorem exists_sq_le_average_on_Icc
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ s ∈ Icc a b,
      |f s| ^ 2 ≤ (b - a)⁻¹ * ∫ x in Icc a b, |f x| ^ 2 ∂volume := by
  have hμ : volume (Icc a b) ≠ 0 := by
    intro hzero
    rw [Real.volume_Icc] at hzero
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hzero
  have hsq : IntegrableOn (fun x => |f x| ^ 2) (Icc a b) volume :=
    ((hf.abs).pow 2).integrableOn_Icc
  have hμtop : volume (Icc a b) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨s, hs, hsbound⟩ :=
    exists_le_setAverage hμ hμtop hsq
  refine ⟨s, hs, ?_⟩
  simpa only [setAverage_eq, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul] using hsbound

/-- A continuous scalar function is in `L²` on every closed bounded
interval. -/
theorem memLp_two_on_Icc_of_continuous
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Icc a b)) := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc a b)) :=
    hf.continuousOn.aestronglyMeasurable measurableSet_Icc
  have hsq : IntegrableOn (fun x => f x ^ 2) (Icc a b) volume :=
    (hf.pow 2).integrableOn_Icc
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

private theorem sq_abs_sub_le_length_mul_setIntegral_deriv_of_le
    {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    |f t - f s| ^ 2 ≤
      (b - a) * ∫ x in Icc a b, |deriv f x| ^ (2 : ℝ) ∂volume := by
  have hderivContinuous : Continuous (deriv f) := hf.continuous_deriv_one
  have hderivIntegrable : IntegrableOn (deriv f) (Icc a b) volume :=
    hderivContinuous.integrableOn_Icc
  have hderivMemLp : MemLp (deriv f) 2 (volume.restrict (Icc a b)) :=
    memLp_two_on_Icc_of_continuous hderivContinuous
  have hderivSmall : MemLp (deriv f) 2 (volume.restrict (Icc s t)) :=
    hderivMemLp.mono_measure
      (Measure.restrict_mono (Icc_subset_Icc hs.1 ht.2) le_rfl)
  have hprimitive := sq_abs_intervalPrimitive_sub_le_l2 hderivIntegrable hs ht hst hderivSmall
  have hftc : ∫ x in s..t, deriv f x = f t - f s :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hf.differentiable (by norm_num) x)
      hderivContinuous.continuousOn.intervalIntegrable
  have hinc : intervalPrimitive a (deriv f) t - intervalPrimitive a (deriv f) s = f t - f s :=
    (intervalPrimitive_sub_eq_intervalIntegral hderivIntegrable hs ht).trans hftc
  rw [hinc] at hprimitive
  have hmono : ∫ x in Icc s t, |deriv f x| ^ (2 : ℝ) ∂volume ≤
      ∫ x in Icc a b, |deriv f x| ^ (2 : ℝ) ∂volume := by
    refine setIntegral_mono_set ?_ ?_ ?_
    · simpa only [Real.norm_eq_abs] using!
        hderivMemLp.integrable_norm_rpow (by norm_num) (by norm_num)
    · exact Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (deriv f x)) _
    · exact Filter.Eventually.of_forall fun x hx => Icc_subset_Icc hs.1 ht.2 hx
  have hlength : 0 ≤ t - s := sub_nonneg.mpr hst
  calc
    |f t - f s| ^ 2 ≤
        (t - s) * ∫ x in Icc s t, |deriv f x| ^ (2 : ℝ) ∂volume := hprimitive
    _ ≤ (t - s) * ∫ x in Icc a b, |deriv f x| ^ (2 : ℝ) ∂volume :=
      mul_le_mul_of_nonneg_left hmono hlength
    _ ≤ (b - a) * ∫ x in Icc a b, |deriv f x| ^ (2 : ℝ) ∂volume := by
      refine mul_le_mul_of_nonneg_right (sub_le_sub ht.2 hs.1) ?_
      exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg (deriv f x)) _
    _ = _ := rfl

private theorem sq_abs_sub_le_length_mul_setIntegral_deriv
    {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    |f t - f s| ^ 2 ≤
      (b - a) * ∫ x in Icc a b, |deriv f x| ^ (2 : ℝ) ∂volume := by
  rcases le_total s t with hst | hts
  · exact sq_abs_sub_le_length_mul_setIntegral_deriv_of_le hs ht hst hf
  · simpa only [abs_sub_comm] using
      sq_abs_sub_le_length_mul_setIntegral_deriv_of_le ht hs hts hf

/-- A quantitative one-dimensional `L²`--`C⁰` bridge on a nondegenerate
closed interval.  Both length factors are displayed explicitly. -/
theorem sq_abs_le_two_inv_length_mul_setIntegral_add_two_length_mul_setIntegral_deriv
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    |f t| ^ 2 ≤
      2 * ((b - a)⁻¹ * ∫ x in Icc a b, |f x| ^ 2 ∂volume) +
        2 * ((b - a) * ∫ x in Icc a b, |deriv f x| ^ (2 : ℝ) ∂volume) := by
  obtain ⟨s, hs, hsbound⟩ := exists_sq_le_average_on_Icc hab hf.continuous
  have hdiff := sq_abs_sub_le_length_mul_setIntegral_deriv hs ht hf
  have htri : |f t| ≤ |f s| + |f t - f s| := by
    calc
      |f t| = |f s + (f t - f s)| := by
        congr 1
        ring
      _ ≤ |f s| + |f t - f s| := abs_add_le (f s) (f t - f s)
  have hsquare : |f t| ^ 2 ≤ 2 * |f s| ^ 2 + 2 * |f t - f s| ^ 2 := by
    calc
      |f t| ^ 2 ≤ (|f s| + |f t - f s|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr htri
      _ ≤ 2 * |f s| ^ 2 + 2 * |f t - f s| ^ 2 := by
        nlinarith [sq_nonneg (|f s| - |f t - f s|)]
  exact hsquare.trans <|
    add_le_add
      (mul_le_mul_of_nonneg_left hsbound (by norm_num))
      (mul_le_mul_of_nonneg_left hdiff (by norm_num))

/-- A smooth sequence which is Cauchy for the explicitly length-weighted
one-dimensional `W¹,²` control is uniformly Cauchy on the closed interval. -/
theorem uniformCauchySeqOn_of_weightedW12Cauchy
    {a b : ℝ} (hab : a < b) {F : ℕ → ℝ → ℝ}
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      2 * ((b - a)⁻¹ * ∫ x in Icc a b, |F m x - F n x| ^ 2 ∂volume) +
        2 * ((b - a) *
          ∫ x in Icc a b, |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ) ∂volume) < ε) :
    UniformCauchySeqOn F Filter.atTop (Icc a b) := by
  refine (Metric.uniformCauchySeqOn_iff (β := ℕ) (F := F) (s := Icc a b)).mpr ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hCauchy (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  have hbound :=
    sq_abs_le_two_inv_length_mul_setIntegral_add_two_length_mul_setIntegral_deriv
      hab ht ((hF m).sub (hF n))
  have hsquare : |F m t - F n t| ^ 2 < ε ^ 2 :=
    hbound.trans_lt (hN m hm n hn)
  have habs : |F m t - F n t| < ε :=
    (sq_lt_sq₀ (abs_nonneg _) hε.le).mp hsquare
  simpa only [Real.dist_eq] using habs

/-- Smooth functions which converge to fixed value and derivative data in
the two interval `L²` energies are uniformly Cauchy.  Integrability of the
displayed error squares is explicit, so nonintegrable Bochner slices cannot
be mistaken for zero energy. -/
theorem uniformCauchySeqOn_of_tendsto_setIntegral_sq_error
    {a b : ℝ} (hab : a < b)
    {F : ℕ → ℝ → ℝ} {u g : ℝ → ℝ}
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hValueIntegrable : ∀ n,
      IntegrableOn (fun x => |F n x - u x| ^ 2) (Icc a b))
    (hDerivIntegrable : ∀ n,
      IntegrableOn
        (fun x => |deriv (F n) x - g x| ^ (2 : ℝ))
        (Icc a b))
    (hValue :
      Tendsto
        (fun n => ∫ x in Icc a b, |F n x - u x| ^ 2)
        atTop (𝓝 0))
    (hDeriv :
      Tendsto
        (fun n =>
          ∫ x in Icc a b,
            |deriv (F n) x - g x| ^ (2 : ℝ))
        atTop (𝓝 0)) :
    UniformCauchySeqOn F atTop (Icc a b) := by
  apply uniformCauchySeqOn_of_weightedW12Cauchy hab hF
  intro ε hε
  let L : ℝ := b - a
  let K : ℝ := L⁻¹ + L
  have hL : 0 < L := by
    simpa only [L] using sub_pos.mpr hab
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  let δ : ℝ := ε / (8 * K)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hValueSmall :
      ∀ᶠ n in atTop,
        (∫ x in Icc a b, |F n x - u x| ^ 2) < δ :=
    (tendsto_order.1 hValue).2 δ hδ
  have hDerivSmall :
      ∀ᶠ n in atTop,
        (∫ x in Icc a b,
          |deriv (F n) x - g x| ^ (2 : ℝ)) < δ :=
    (tendsto_order.1 hDeriv).2 δ hδ
  obtain ⟨N, hN⟩ :=
    (eventually_atTop.1 (hValueSmall.and hDerivSmall))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmSmall := hN m hm
  have hnSmall := hN n hn
  have hValueDiffIntegrable :
      IntegrableOn
        (fun x => |F m x - F n x| ^ 2) (Icc a b) :=
    ((hF m).continuous.sub (hF n).continuous).abs.pow 2
      |>.integrableOn_Icc
  have hValueUpperIntegrable :
      IntegrableOn
        (fun x =>
          2 * |F m x - u x| ^ 2 +
            2 * |F n x - u x| ^ 2)
        (Icc a b) :=
    ((hValueIntegrable m).const_mul 2).add
      ((hValueIntegrable n).const_mul 2)
  have hValueDiff :
      (∫ x in Icc a b, |F m x - F n x| ^ 2) ≤
        2 * (∫ x in Icc a b, |F m x - u x| ^ 2) +
          2 * (∫ x in Icc a b, |F n x - u x| ^ 2) := by
    calc
      (∫ x in Icc a b, |F m x - F n x| ^ 2) ≤
          ∫ x in Icc a b,
            2 * |F m x - u x| ^ 2 +
              2 * |F n x - u x| ^ 2 := by
        refine setIntegral_mono_on
          hValueDiffIntegrable hValueUpperIntegrable
          measurableSet_Icc ?_
        intro x _
        rw [sq_abs, sq_abs, sq_abs]
        nlinarith [sq_nonneg
          ((F m x - u x) + (F n x - u x))]
      _ =
          2 * (∫ x in Icc a b, |F m x - u x| ^ 2) +
            2 * (∫ x in Icc a b, |F n x - u x| ^ 2) := by
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact (hValueIntegrable m).const_mul 2
        · exact (hValueIntegrable n).const_mul 2
  have hDerivSub (x : ℝ) :
      deriv (fun y => F m y - F n y) x =
        deriv (F m) x - deriv (F n) x := by
    exact deriv_sub
      ((hF m).differentiable (by norm_num) x)
      ((hF n).differentiable (by norm_num) x)
  have hDerivDiffIntegrable :
      IntegrableOn
        (fun x =>
          |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ))
        (Icc a b) := by
    have hcontinuous :
        Continuous
          (deriv (fun y => F m y - F n y)) :=
      ((hF m).sub (hF n)).continuous_deriv_one
    simpa only [Real.rpow_two] using!
      (hcontinuous.abs.pow 2).integrableOn_Icc
  have hDerivUpperIntegrable :
      IntegrableOn
        (fun x =>
          2 * |deriv (F m) x - g x| ^ (2 : ℝ) +
            2 * |deriv (F n) x - g x| ^ (2 : ℝ))
        (Icc a b) :=
    ((hDerivIntegrable m).const_mul 2).add
      ((hDerivIntegrable n).const_mul 2)
  have hDerivDiff :
      (∫ x in Icc a b,
          |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ)) ≤
        2 * (∫ x in Icc a b,
          |deriv (F m) x - g x| ^ (2 : ℝ)) +
        2 * (∫ x in Icc a b,
          |deriv (F n) x - g x| ^ (2 : ℝ)) := by
    calc
      (∫ x in Icc a b,
          |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ)) ≤
          ∫ x in Icc a b,
            2 * |deriv (F m) x - g x| ^ (2 : ℝ) +
              2 * |deriv (F n) x - g x| ^ (2 : ℝ) := by
        refine setIntegral_mono_on
          hDerivDiffIntegrable hDerivUpperIntegrable
          measurableSet_Icc ?_
        intro x _
        rw [hDerivSub, Real.rpow_two, Real.rpow_two,
          Real.rpow_two, sq_abs, sq_abs, sq_abs]
        nlinarith [sq_nonneg
          ((deriv (F m) x - g x) +
            (deriv (F n) x - g x))]
      _ =
          2 * (∫ x in Icc a b,
            |deriv (F m) x - g x| ^ (2 : ℝ)) +
          2 * (∫ x in Icc a b,
            |deriv (F n) x - g x| ^ (2 : ℝ)) := by
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact (hDerivIntegrable m).const_mul 2
        · exact (hDerivIntegrable n).const_mul 2
  have hValueDiffSmall :
      (∫ x in Icc a b, |F m x - F n x| ^ 2) < 4 * δ := by
    calc
      (∫ x in Icc a b, |F m x - F n x| ^ 2) ≤
          2 * (∫ x in Icc a b, |F m x - u x| ^ 2) +
            2 * (∫ x in Icc a b, |F n x - u x| ^ 2) :=
        hValueDiff
      _ < 4 * δ := by linarith [hmSmall.1, hnSmall.1]
  have hDerivDiffSmall :
      (∫ x in Icc a b,
          |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ)) <
        4 * δ := by
    calc
      (∫ x in Icc a b,
          |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ)) ≤
          2 * (∫ x in Icc a b,
            |deriv (F m) x - g x| ^ (2 : ℝ)) +
          2 * (∫ x in Icc a b,
            |deriv (F n) x - g x| ^ (2 : ℝ)) :=
        hDerivDiff
      _ < 4 * δ := by linarith [hmSmall.2, hnSmall.2]
  have hLInv : 0 < L⁻¹ := inv_pos.mpr hL
  calc
    2 * ((b - a)⁻¹ *
        ∫ x in Icc a b, |F m x - F n x| ^ 2) +
        2 * ((b - a) *
          ∫ x in Icc a b,
            |deriv (fun y => F m y - F n y) x| ^ (2 : ℝ)) <
      2 * (L⁻¹ * (4 * δ)) +
        2 * (L * (4 * δ)) := by
          dsimp only [L]
          gcongr
    _ = ε := by
      dsimp only [δ, K]
      field_simp
      norm_num

end

end PDE
