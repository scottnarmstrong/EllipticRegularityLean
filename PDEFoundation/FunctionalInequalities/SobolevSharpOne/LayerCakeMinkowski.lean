module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Layer-cake Minkowski inequality

For a nonnegative measurable `f` and `1 ≤ q < ∞`,
`(∫ f^q)^{1/q} ≤ ∫_0^∞ μ{f > s}^{1/q} ds`.  The finite case is proved by Hölder duality
against `f^{q-1}`; the general case by truncation along a spanning sequence of finite-measure sets.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.SobolevSharp

open MeasureTheory Set

/-- The inner Tonelli identity: `a^q = ∫_0^∞ 1_{s < a} a^{q-1} ds`. -/
theorem rpow_eq_lintegral_Ioi_indicator_lt (a : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ENNReal.ofReal a ^ q =
      ∫⁻ s in Ioi (0 : ℝ), (Iio a).indicator (fun _ => ENNReal.ofReal a ^ (q - 1)) s := by
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    setLIntegral_const, Iio_inter_Ioi, Real.volume_Ioo, sub_zero, mul_comm]
  conv_lhs => rw [show q = 1 + (q - 1) by ring]
  rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (sub_nonneg.mpr hq), ENNReal.rpow_one]

variable {α : Type*} [MeasurableSpace α]

/-- The Minkowski bound when `∫ f^q` is finite. -/
theorem lintegral_rpow_le_pow_of_ne_top (μ : Measure α) [SFinite μ] {f : α → ℝ}
    (hf : Measurable f) {q : ℝ} (hq : 1 < q)
    (hA : ∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ ≠ ∞) :
    ∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ ≤
      (∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q)) ^ q := by
  set A := ∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ with hAdef
  set T := ∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q) with hT
  have hc : q.HolderConjugate (Real.conjExponent q) := Real.HolderConjugate.conjExponent hq
  set q' := Real.conjExponent q with hq'
  set h : α → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) ^ (q - 1) with hh
  have hhm : Measurable h := (ENNReal.measurable_ofReal.comp hf).pow_const _
  have hhA : ∫⁻ x, h x ^ q' ∂μ = A := by
    refine lintegral_congr fun x => ?_
    rw [hh, ← ENNReal.rpow_mul, hc.sub_one_mul_conj]
  -- Tonelli
  have hK : Measurable (Function.uncurry fun (x : α) (s : ℝ) =>
      (Iio (f x)).indicator (fun _ => h x) s) := by
    have : (Function.uncurry fun (x : α) (s : ℝ) =>
        (Iio (f x)).indicator (fun _ => h x) s) =
        {p : α × ℝ | p.2 < f p.1}.indicator (fun p => h p.1) := by
      funext p
      simp [Set.indicator, Function.uncurry]
    rw [this]
    exact (hhm.comp measurable_fst).indicator
      (measurableSet_lt measurable_snd (hf.comp measurable_fst))
  have hswap : A = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x, (Iio (f x)).indicator (fun _ => h x) s ∂μ := by
    rw [hAdef, ← lintegral_lintegral_swap hK.aemeasurable]
    exact lintegral_congr fun x => rpow_eq_lintegral_Ioi_indicator_lt (f x) hq.le
  have hinner : ∀ s : ℝ, ∫⁻ x, (Iio (f x)).indicator (fun _ => h x) s ∂μ ≤
      μ {a | s < f a} ^ (1 / q) * A ^ (1 / q') := by
    intro s
    have hE : MeasurableSet {a | s < f a} := measurableSet_lt measurable_const hf
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
      (f := {a | s < f a}.indicator 1) (g := h) (measurable_one.indicator hE).aemeasurable
      hhm.aemeasurable
    have h1 : ∫⁻ a, ({a | s < f a}.indicator (1 : α → ℝ≥0∞) a) ^ q ∂μ = μ {a | s < f a} := by
      have : ∀ a, ({a | s < f a}.indicator (1 : α → ℝ≥0∞) a) ^ q =
          {a | s < f a}.indicator 1 a := by
        intro a
        by_cases ha : a ∈ {a | s < f a}
        · simp [Set.indicator_of_mem ha]
        · simp [Set.indicator_of_notMem ha, ENNReal.zero_rpow_of_pos (by linarith : 0 < q)]
      rw [lintegral_congr this, lintegral_indicator_one hE]
    have h2 : ∫⁻ x, (Iio (f x)).indicator (fun _ => h x) s ∂μ =
        ∫⁻ a, ({a | s < f a}.indicator (1 : α → ℝ≥0∞) * h) a ∂μ := by
      refine lintegral_congr fun x => ?_
      by_cases hx : s < f x
      · have : x ∈ {a | s < f a} := hx
        simp [Set.indicator_of_mem this, Set.indicator_of_mem (show s ∈ Iio (f x) from hx)]
      · have : x ∉ {a | s < f a} := hx
        simp [Set.indicator_of_notMem this,
          Set.indicator_of_notMem (show s ∉ Iio (f x) from hx)]
    rw [h2]
    refine this.trans ?_
    rw [h1, hhA]
  have hA' : A ≤ T * A ^ (1 / q') := by
    calc A = _ := hswap
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q) * A ^ (1 / q') :=
          lintegral_mono hinner
      _ = T * A ^ (1 / q') := by
          rw [hT, lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hc.symm.one_div_nonneg hA)]
  by_cases h0 : A = 0
  · rw [h0]; exact bot_le
  have hsplit : A = A ^ (1 / q) * A ^ (1 / q') := by
    have e : 1 / q + 1 / q' = 1 := by simpa using hc.inv_add_inv_eq_one
    rw [← ENNReal.rpow_add _ _ h0 hA, e, ENNReal.rpow_one]
  have hq'0 : A ^ (1 / q') ≠ 0 := by
    intro hz
    rcases ENNReal.rpow_eq_zero_iff.mp hz with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h0 h1
    · exact absurd h2 (not_lt.mpr hc.symm.one_div_nonneg)
  have hq'top : A ^ (1 / q') ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hc.symm.one_div_nonneg hA
  have hle : A ^ (1 / q) ≤ T := by
    have hh : A ^ (1 / q') * A ^ (1 / q) ≤ A ^ (1 / q') * T := by
      calc A ^ (1 / q') * A ^ (1 / q) = A := by rw [mul_comm]; exact hsplit.symm
        _ ≤ T * A ^ (1 / q') := hA'
        _ = A ^ (1 / q') * T := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_right hq'0 hq'top).mp hh
  calc A = (A ^ (1 / q)) ^ q := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hc.ne_zero, ENNReal.rpow_one]
    _ ≤ T ^ q := ENNReal.rpow_le_rpow hle hc.nonneg

/-- Truncation of `f` to a bounded function supported in the `n`-th spanning set. -/
noncomputable def truncate (μ : Measure α) [SigmaFinite μ] (f : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  (spanningSets μ n).indicator (fun x => min (f x) n) x

theorem measurable_truncate (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f)
    (n : ℕ) : Measurable (truncate μ f n) :=
  by unfold truncate; exact (hf.min measurable_const).indicator (measurableSet_spanningSets μ n)

theorem truncate_nonneg (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf0 : 0 ≤ f) (n : ℕ) :
    0 ≤ truncate μ f n := fun x => by
  unfold truncate
  exact Set.indicator_nonneg (fun y _ => le_min (hf0 y) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)) x

theorem truncate_le (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf0 : 0 ≤ f) (n : ℕ) (x : α) :
    truncate μ f n x ≤ f x := by
  unfold truncate
  by_cases hx : x ∈ spanningSets μ n
  · rw [Set.indicator_of_mem hx]; exact min_le_left _ _
  · rw [Set.indicator_of_notMem hx]; exact hf0 x

theorem truncate_mono (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf0 : 0 ≤ f) :
    Monotone fun n => truncate μ f n := by
  intro m n hmn x
  show truncate μ f m x ≤ truncate μ f n x
  unfold truncate
  by_cases hx : x ∈ spanningSets μ m
  · have hx' : x ∈ spanningSets μ n := monotone_spanningSets μ hmn hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    exact min_le_min le_rfl (by exact_mod_cast hmn)
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ spanningSets μ n
    · rw [Set.indicator_of_mem hx']; exact le_min (hf0 x) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    · rw [Set.indicator_of_notMem hx']

theorem exists_truncate_eq (μ : Measure α) [SigmaFinite μ] (f : α → ℝ) (x : α) :
    ∃ n, truncate μ f n x = f x := by
  obtain ⟨m, hm⟩ : ∃ m, x ∈ spanningSets μ m := by
    have := iUnion_spanningSets μ
    have hx : x ∈ ⋃ i, spanningSets μ i := by rw [this]; trivial
    exact Set.mem_iUnion.mp hx
  obtain ⟨k, hk⟩ := exists_nat_ge (f x)
  refine ⟨max m k, ?_⟩
  unfold truncate
  rw [Set.indicator_of_mem (monotone_spanningSets μ (le_max_left m k) hm)]
  exact min_eq_left (hk.trans (by exact_mod_cast le_max_right m k))

theorem lintegral_rpow_truncate_ne_top (μ : Measure α) [SigmaFinite μ] {f : α → ℝ}
    {q : ℝ} (hq : 0 < q) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (truncate μ f n x) ^ q ∂μ ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ x, (spanningSets μ n).indicator
    (fun _ => ENNReal.ofReal n ^ q) x ∂μ) ?_ ?_
  · rw [lintegral_indicator (measurableSet_spanningSets μ n), setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
      (measure_spanningSets_lt_top μ n).ne
  · refine lintegral_mono fun x => ?_
    unfold truncate
    by_cases hx : x ∈ spanningSets μ n
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (min_le_right _ _)) hq.le
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp [ENNReal.zero_rpow_of_pos hq]

/-- Layer-cake Minkowski inequality, power form. -/
theorem lintegral_rpow_le_lintegral_meas_lt_rpow (μ : Measure α) [SigmaFinite μ] {f : α → ℝ}
    (hf : Measurable f) (hf0 : 0 ≤ f) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ ≤
      (∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q)) ^ q := by
  rcases hq.eq_or_lt with rfl | hq1
  · simp only [ENNReal.rpow_one, div_one]
    exact (lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hf0)
      hf.aemeasurable).le
  have hq0 : 0 < q := by linarith
  have hmono : Monotone fun n => fun x => ENNReal.ofReal (truncate μ f n x) ^ q :=
    fun m n hmn x => ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (truncate_mono μ hf0 hmn x)) hq0.le
  have hsup : ∀ x, ENNReal.ofReal (f x) ^ q =
      ⨆ n, ENNReal.ofReal (truncate μ f n x) ^ q := by
    intro x
    refine le_antisymm ?_ (iSup_le fun n => ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (truncate_le μ hf0 n x)) hq0.le)
    obtain ⟨n, hn⟩ := exists_truncate_eq μ f x
    exact le_iSup_of_le n (by rw [hn])
  have hA : ∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ =
      ⨆ n, ∫⁻ x, ENNReal.ofReal (truncate μ f n x) ^ q ∂μ := by
    have h1 : (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) =
        ∫⁻ x, ⨆ n, ENNReal.ofReal (truncate μ f n x) ^ q ∂μ :=
      lintegral_congr hsup
    rw [h1]
    exact lintegral_iSup (f := fun n x => ENNReal.ofReal (truncate μ f n x) ^ q)
      (fun n => (ENNReal.measurable_ofReal.comp
        (measurable_truncate μ hf n)).pow_const _) hmono
  rw [hA]
  refine iSup_le fun n => ?_
  refine (lintegral_rpow_le_pow_of_ne_top μ (measurable_truncate μ hf n) hq1
    (lintegral_rpow_truncate_ne_top μ hq0 n)).trans ?_
  refine ENNReal.rpow_le_rpow (lintegral_mono fun s => ?_) hq0.le
  refine ENNReal.rpow_le_rpow (measure_mono fun a ha => ?_) (by positivity)
  exact lt_of_lt_of_le ha (truncate_le μ hf0 n a)

/-- Layer-cake Minkowski inequality: `‖f‖_q ≤ ∫_0^∞ μ{f > s}^{1/q} ds`, ENNReal form. -/
theorem lintegral_rpow_rpow_inv_le_lintegral_meas_lt_rpow (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ} (hf : Measurable f) (hf0 : 0 ≤ f) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) ^ (1 / q) ≤
      ∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  calc (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) ^ (1 / q)
      ≤ ((∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q)) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (lintegral_rpow_le_lintegral_meas_lt_rpow μ hf hf0 hq)
          (by positivity)
    _ = _ := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

/-- Layer-cake Minkowski inequality in `eLpNorm` form. -/
theorem eLpNorm_le_lintegral_meas_lt_rpow (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ} (hf : Measurable f) (hf0 : 0 ≤ f) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ ∫⁻ s in Ioi (0 : ℝ), μ {a | s < f a} ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  refine le_trans (le_of_eq ?_) (lintegral_rpow_rpow_inv_le_lintegral_meas_lt_rpow μ hf hf0 hq)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0.le]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x)]

end PDE.SobolevSharp
