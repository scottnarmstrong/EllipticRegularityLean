module

public import PDEFoundation.Analysis.Gehring.TailGlobal
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Layer-cake (Tonelli) identities for the truncated absorption

`lintegral_layer`: for `p > 0`, `L > 0`,
`∫_{t ∈ (0,L)} p t^{p-1} ∫_{{Φ > t}} w = ∫ w · min(Φ, L)^p`.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem lintegral_Ioo_rpow {a M : ℝ} (ha : -1 < a) (hM : 0 ≤ M) :
    ∫⁻ t in Ioo 0 M, ENNReal.ofReal (t ^ a) = ENNReal.ofReal (M ^ (a + 1) / (a + 1)) := by
  rw [setLIntegral_congr Ioo_ae_eq_Ioc]
  have hint : IntegrableOn (fun t : ℝ => t ^ a) (Ioc 0 M) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).1
      (intervalIntegral.intervalIntegrable_rpow' ha)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 M)] fun t : ℝ => t ^ a :=
    (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun t ht => Real.rpow_nonneg ht.1.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hM,
    integral_rpow (Or.inl ha)]
  have : (0 : ℝ) ^ (a + 1) = 0 := Real.zero_rpow (by linarith)
  rw [this, sub_zero]

theorem lintegral_layer_pt {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (a : ℝ≥0∞) :
    ∫⁻ t in Ioo 0 L, ENNReal.ofReal (p * t ^ (p - 1)) *
        (if ENNReal.ofReal t < a then 1 else 0) =
      (min a (ENNReal.ofReal L)) ^ p := by
  set m := min a (ENNReal.ofReal L) with hm
  have hmfin : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  set M := m.toReal with hMdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hML : M ≤ L := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right a (ENNReal.ofReal L))
    rwa [ENNReal.toReal_ofReal hL.le] at this
  have hkey : ∀ t ∈ Ioo 0 L, (ENNReal.ofReal t < a ↔ t < M) := by
    intro t ht
    rw [hMdef, ← ENNReal.ofReal_lt_iff_lt_toReal ht.1.le hmfin, hm, lt_min_iff]
    exact ⟨fun h => ⟨h, (ENNReal.ofReal_lt_ofReal_iff hL).2 ht.2⟩, fun h => h.1⟩
  have h1 : ∫⁻ t in Ioo 0 L, ENNReal.ofReal (p * t ^ (p - 1)) *
        (if ENNReal.ofReal t < a then 1 else 0) =
      ∫⁻ t in Ioo 0 L, (Iio M).indicator (fun t => ENNReal.ofReal (p * t ^ (p - 1))) t := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    by_cases h : t < M
    · have := (hkey t ht).2 h
      rw [Set.indicator_of_mem (show t ∈ Iio M from h)]
      simp [this]
    · have : ¬ ENNReal.ofReal t < a := fun h' => h ((hkey t ht).1 h')
      rw [Set.indicator_of_notMem (show t ∉ Iio M from h)]
      simp [this]
  rw [h1, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio M ∩ Ioo 0 L = Ioo 0 M := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, lt_of_lt_of_le h1 hML⟩
  rw [hset]
  have hpe : ∀ t : ℝ, ENNReal.ofReal (p * t ^ (p - 1)) =
      ENNReal.ofReal p * ENNReal.ofReal (t ^ (p - 1)) := fun t => ENNReal.ofReal_mul hp.le
  simp_rw [hpe]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ioo_rpow (by linarith) hM0, ← ENNReal.ofReal_mul hp.le,
    show p - 1 + 1 = p by ring, mul_div_cancel₀ _ hp.ne', ← ENNReal.ofReal_rpow_of_nonneg hM0 hp.le,
    hMdef, ENNReal.ofReal_toReal hmfin]

/-- **Layer-cake / Tonelli identity.** For a.e. measurable `Φ, w : Vec d → ℝ≥0∞`,
`∫_{t ∈ (0,L)} p t^{p-1} ∫_{{t < Φ}} w = ∫ w · min(Φ, L)^p`. -/
theorem lintegral_layer {Φ w : Vec d → ℝ≥0∞} (hΦ : AEMeasurable Φ volume)
    (hw : AEMeasurable w volume) {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    ∫⁻ t in Ioo 0 L, ENNReal.ofReal (p * t ^ (p - 1)) *
        ∫⁻ x in {x | ENNReal.ofReal t < Φ x}, w x =
      ∫⁻ x, w x * (min (Φ x) (ENNReal.ofReal L)) ^ p := by
  set Φ' := hΦ.mk Φ with hΦ'
  set w' := hw.mk w with hw'
  have hΦm : Measurable Φ' := hΦ.measurable_mk
  have hwm : Measurable w' := hw.measurable_mk
  have hΦae : Φ =ᵐ[volume] Φ' := hΦ.ae_eq_mk
  have hwae : w =ᵐ[volume] w' := hw.ae_eq_mk
  -- replace by measurable versions
  have e1 : ∀ t : ℝ, ∫⁻ x in {x | ENNReal.ofReal t < Φ x}, w x =
      ∫⁻ x in {x | ENNReal.ofReal t < Φ' x}, w' x := by
    intro t
    rw [setLIntegral_congr (t := {x | ENNReal.ofReal t < Φ' x})
      (by filter_upwards [hΦae] with x hx using by simp [hx])]
    exact lintegral_congr_ae (ae_restrict_of_ae hwae)
  have e2 : ∫⁻ x, w x * (min (Φ x) (ENNReal.ofReal L)) ^ p =
      ∫⁻ x, w' x * (min (Φ' x) (ENNReal.ofReal L)) ^ p := by
    refine lintegral_congr_ae ?_
    filter_upwards [hΦae, hwae] with x h1 h2
    rw [h1, h2]
  simp_rw [e1]
  rw [e2]
  have e3 : ∀ t : ℝ, ENNReal.ofReal (p * t ^ (p - 1)) * ∫⁻ x in {x | ENNReal.ofReal t < Φ' x}, w' x
      = ∫⁻ x, w' x * (ENNReal.ofReal (p * t ^ (p - 1)) *
          (if ENNReal.ofReal t < Φ' x then 1 else 0)) := by
    intro t
    have hS : MeasurableSet {x | ENNReal.ofReal t < Φ' x} :=
      measurableSet_lt measurable_const hΦm
    rw [← lintegral_indicator hS, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    by_cases h : ENNReal.ofReal t < Φ' x
    · simp [h, mul_comm]
    · simp [h]
  simp_rw [e3]
  have hjm : Measurable (Function.uncurry fun (t : ℝ) (x : Vec d) => w' x *
      (ENNReal.ofReal (p * t ^ (p - 1)) * (if ENNReal.ofReal t < Φ' x then 1 else 0))) := by
    have hS : MeasurableSet {q : ℝ × Vec d | ENNReal.ofReal q.1 < Φ' q.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hΦm.comp measurable_snd)
    have : Measurable fun q : ℝ × Vec d => (if ENNReal.ofReal q.1 < Φ' q.2 then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite hS measurable_const measurable_const
    have h2 : Measurable fun q : ℝ × Vec d => ENNReal.ofReal (q.1 ^ (p - 1) * p) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst.pow_const _).mul_const _
    show Measurable fun q : ℝ × Vec d => w' q.2 *
      (ENNReal.ofReal (p * q.1 ^ (p - 1)) * (if ENNReal.ofReal q.1 < Φ' q.2 then 1 else 0))
    refine (hwm.comp measurable_snd).mul (Measurable.mul ?_ this)
    simpa [mul_comm] using h2
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hm1 : Measurable fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  have hm2 : Measurable fun t : ℝ => (if ENNReal.ofReal t < Φ' x then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
      measurable_const measurable_const
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 1)) *
      (if ENNReal.ofReal t < Φ' x then (1 : ℝ≥0∞) else 0) := hm1.mul hm2
  rw [lintegral_const_mul'' _ hm.aemeasurable, lintegral_layer_pt hp hL]

end PDE.Gehring
