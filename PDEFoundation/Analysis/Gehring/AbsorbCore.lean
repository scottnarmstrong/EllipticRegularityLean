module

public import PDEFoundation.Analysis.Gehring.AbsorbLayer

/-!
# The core computation of the truncated absorption

`I_L = ∫ g min(g,L)^ε` and the bound
`∫_{t∈(0,L)} t^{ε-θ} ∫_{g > c t} g^θ ≤ (c^{-(1-θ+ε)} / (1-θ+ε)) I_L`, with `c = 2^{-1/θ}`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The truncated moment `I_L = ∫ g · min(g, L)^ε`. -/
noncomputable def truncMoment (g : Vec d → ℝ) (L ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (g x) * (min (ENNReal.ofReal (g x)) (ENNReal.ofReal L)) ^ ε

/-- The truncated maximal function `V_L = min(V, L)`. -/
noncomputable def truncV (g : Vec d → ℝ) (L : ℝ) (x : Vec d) : ℝ≥0∞ :=
  min (gehringV g x) (ENNReal.ofReal L)

open Classical in
theorem lintegral_swap_layer {S : Set (ℝ × Vec d)} (hS : MeasurableSet S) {w : Vec d → ℝ≥0∞}
    (hw : Measurable w) {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) (L : ℝ) :
    ∫⁻ t in Ioo 0 L, κ t * ∫⁻ x in {x | (t, x) ∈ S}, w x =
      ∫⁻ x, w x * ∫⁻ t in Ioo 0 L, κ t * (if (t, x) ∈ S then 1 else 0) := by
  have e3 : ∀ t : ℝ, κ t * ∫⁻ x in {x | (t, x) ∈ S}, w x =
      ∫⁻ x, w x * (κ t * (if (t, x) ∈ S then 1 else 0)) := by
    intro t
    have hSt : MeasurableSet {x | (t, x) ∈ S} := measurable_prodMk_left hS
    rw [← lintegral_indicator hSt, ← lintegral_const_mul _ (hw.indicator hSt)]
    refine lintegral_congr fun x => ?_
    by_cases h : (t, x) ∈ S
    · simp [h, mul_comm]
    · simp [h]
  simp_rw [e3]
  have hind : Measurable fun q : ℝ × Vec d => (if q ∈ S then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite hS measurable_const measurable_const
  have hjm : Measurable (Function.uncurry fun (t : ℝ) (x : Vec d) =>
      w x * (κ t * (if (t, x) ∈ S then 1 else 0))) :=
    (hw.comp measurable_snd).mul ((hκ.comp measurable_fst).mul hind)
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun t : ℝ => κ t * (if (t, x) ∈ S then (1 : ℝ≥0∞) else 0) :=
    hκ.mul (hind.comp (measurable_prodMk_right))
  rw [lintegral_const_mul _ hm]

/-- The inner `t`-integral: `∫_{(0,L)} t^a · 1{c t < A} = (min(L, A/c))^{a+1}/(a+1)`. -/
theorem lintegral_rpow_ite {a L c A : ℝ} (ha : -1 < a) (hL : 0 < L) (hc : 0 < c) (hA : 0 ≤ A) :
    ∫⁻ t in Ioo 0 L, ENNReal.ofReal (t ^ a) * (if c * t < A then 1 else 0) =
      ENNReal.ofReal (min L (A / c) ^ (a + 1) / (a + 1)) := by
  have h1 : ∫⁻ t in Ioo 0 L, ENNReal.ofReal (t ^ a) * (if c * t < A then 1 else 0) =
      ∫⁻ t in Ioo 0 L, (Iio (A / c)).indicator (fun t => ENNReal.ofReal (t ^ a)) t := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    have hiff : c * t < A ↔ t < A / c := by rw [lt_div_iff₀ hc, mul_comm]
    by_cases h : t < A / c
    · rw [Set.indicator_of_mem (show t ∈ Iio (A / c) from h)]
      simp [hiff.2 h]
    · rw [Set.indicator_of_notMem (show t ∉ Iio (A / c) from h)]
      simp [mt hiff.1 h]
  rw [h1, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio (A / c) ∩ Ioo 0 L = Ioo 0 (min L (A / c)) := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioo, lt_min_iff]
    tauto
  rw [hset]
  exact lintegral_Ioo_rpow ha (le_min hL.le (by positivity))

/-- The pointwise real inequality behind the core bound. -/
theorem real_core (hd : 0 < d) {x L ε : ℝ} (hx : 0 ≤ x) (hL : 0 < L) (hε : 0 < ε) :
    x ^ gehringTheta d *
        (min L (x / gehringC d)) ^ (1 - gehringTheta d + ε) ≤
      gehringC d ^ (-(1 - gehringTheta d + ε)) * (x * (min x L) ^ ε) := by
  have hθ := gehringTheta_pos hd
  have hθ1 := gehringTheta_lt_one d
  have hc := gehringC_pos d
  have hc1 := gehringC_le_one hd
  set c := gehringC d with hcdef
  set θ := gehringTheta d with hθdef
  set b := 1 - θ + ε with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  set u := min x L with hu
  have hu0 : 0 ≤ u := le_min hx hL.le
  have hm0 : 0 ≤ min L (x / c) := le_min hL.le (by positivity)
  have hm : min L (x / c) ≤ u / c := by
    rw [le_div_iff₀ hc]
    refine le_min ?_ ?_
    · calc min L (x / c) * c ≤ (x / c) * c := by
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hc.le
        _ = x := by field_simp
    · calc min L (x / c) * c ≤ L * c := mul_le_mul_of_nonneg_right (min_le_left _ _) hc.le
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left hc1 hL.le
        _ = L := mul_one L
  have h1 : (min L (x / c)) ^ b ≤ c ^ (-b) * u ^ b := by
    calc (min L (x / c)) ^ b ≤ (u / c) ^ b := Real.rpow_le_rpow hm0 hm hbpos.le
      _ = c ^ (-b) * u ^ b := by
          rw [Real.div_rpow hu0 hc.le, Real.rpow_neg hc.le]; ring
  have h2 : u ^ b = u ^ (1 - θ) * u ^ ε := by
    rw [hb, Real.rpow_add' hu0 (by linarith)]
  have h3 : x ^ θ * u ^ (1 - θ) ≤ x := by
    calc x ^ θ * u ^ (1 - θ) ≤ x ^ θ * x ^ (1 - θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx _)
          exact Real.rpow_le_rpow hu0 (min_le_left _ _) (by linarith)
      _ = x := by
          rw [← Real.rpow_add' hx (by linarith), show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  calc x ^ θ * (min L (x / c)) ^ b ≤ x ^ θ * (c ^ (-b) * u ^ b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx _)
    _ = c ^ (-b) * ((x ^ θ * u ^ (1 - θ)) * u ^ ε) := by rw [h2]; ring
    _ ≤ c ^ (-b) * (x * u ^ ε) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc.le _)
        exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hu0 _)

theorem truncMoment_integrand_eq {x ε L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    ENNReal.ofReal x * (min (ENNReal.ofReal x) (ENNReal.ofReal L)) ^ ε =
      ENNReal.ofReal (x * (min x L) ^ ε) := by
  rw [← ENNReal.ofReal_min, ENNReal.ofReal_rpow_of_nonneg (le_min hx hL) hε,
    ← ENNReal.ofReal_mul hx]

open Classical in
/-- **Core bound**: `∫_{t∈(0,L)} t^{ε-θ} ∫_{g > c t} g^θ ≤ (c^{-b}/b) I_L`, `b = 1-θ+ε`. -/
theorem core_bound (hd : 0 < d) {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgm : Measurable g)
    {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    ∫⁻ t in Ioo 0 L, ENNReal.ofReal (t ^ (ε - gehringTheta d)) *
        (∫⁻ y in {y | gehringC d * t < g y}, ENNReal.ofReal (g y ^ gehringTheta d)) ≤
      ENNReal.ofReal (gehringC d ^ (-(1 - gehringTheta d + ε)) / (1 - gehringTheta d + ε)) *
        truncMoment g L ε := by
  have hθ := gehringTheta_pos hd
  have hθ1 := gehringTheta_lt_one d
  have hc := gehringC_pos d
  set c := gehringC d with hcdef
  set θ := gehringTheta d with hθdef
  set b := 1 - θ + ε with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  have hS : MeasurableSet {q : ℝ × Vec d | c * q.1 < g q.2} :=
    measurableSet_lt (measurable_fst.const_mul c) (hgm.comp measurable_snd)
  have hw : Measurable fun y => ENNReal.ofReal (g y ^ θ) :=
    ENNReal.measurable_ofReal.comp (hgm.pow_const _)
  have hκ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (ε - θ)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hswap := lintegral_swap_layer hS hw hκ L
  refine (le_of_eq hswap).trans ?_
  have hpt : ∀ y, ENNReal.ofReal (g y ^ θ) * ∫⁻ t in Ioo 0 L, ENNReal.ofReal (t ^ (ε - θ)) *
      (if (t, y) ∈ {q : ℝ × Vec d | c * q.1 < g q.2} then 1 else 0) ≤
      ENNReal.ofReal (c ^ (-b) / b) *
        (ENNReal.ofReal (g y) * (min (ENNReal.ofReal (g y)) (ENNReal.ofReal L)) ^ ε) := by
    intro y
    have hin : ∫⁻ t in Ioo 0 L, ENNReal.ofReal (t ^ (ε - θ)) *
        (if (t, y) ∈ {q : ℝ × Vec d | c * q.1 < g q.2} then 1 else 0) =
        ENNReal.ofReal (min L (g y / c) ^ (ε - θ + 1) / (ε - θ + 1)) := by
      rw [← lintegral_rpow_ite (by linarith) hL hc (hg0 y)]
      refine lintegral_congr fun t => ?_
      simp only [Set.mem_ofPred_eq]
    rw [hin, truncMoment_integrand_eq (hg0 y) hL.le hε.le,
      show ε - θ + 1 = b by rw [hb]; ring, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hg0 y) _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := real_core hd (hg0 y) hL hε
    calc g y ^ θ * (min L (g y / c) ^ b / b) = (g y ^ θ * min L (g y / c) ^ b) / b := by ring
      _ ≤ (c ^ (-b) * (g y * min (g y) L ^ ε)) / b := by gcongr
      _ = _ := by ring
  refine (lintegral_mono hpt).trans ?_
  rw [truncMoment, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end PDE.Gehring
