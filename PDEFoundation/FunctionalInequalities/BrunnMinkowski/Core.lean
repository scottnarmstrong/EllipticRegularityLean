module

public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.Induction
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Brunn--Minkowski from Prékopa--Leindler

The nondegenerate case (both volumes positive) of the Brunn--Minkowski inequality for compact
sets, obtained by applying the `[0,∞]`-valued Prékopa--Leindler inequality to indicators of
`l⁻¹ A`, `(1-l)⁻¹ B` and `A + B`, together with the degenerate cases.
-/

@[expose] public section

namespace PDE.BrunnMinkowskiProof

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- Translating a nonempty `A` by an element of `B`: `|A| ≤ |A + B|`. -/
theorem volume_le_add_right {A B : Set (Vec d)} {b : Vec d} (hb : b ∈ B) :
    volume A ≤ volume (A + B) := by
  calc volume A = volume (b +ᵥ A) := (measure_vadd _ _ _).symm
    _ ≤ volume (A + B) := by
      refine measure_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, hk, b, hb, by simp [add_comm]⟩

/-- `|B| ≤ |A + B|` for `a ∈ A`. -/
theorem volume_le_add_left {A B : Set (Vec d)} {a : Vec d} (ha : a ∈ A) :
    volume B ≤ volume (A + B) := by
  calc volume B = volume (a +ᵥ B) := (measure_vadd _ _ _).symm
    _ ≤ volume (A + B) := by
      refine measure_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨a, ha, k, hk, rfl⟩

/-- Real arithmetic: with `l = α / (α + β)`, `l⁻¹ ^ d * α ^ d = (α + β) ^ d`. -/
theorem inv_pow_mul {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (α / (α + β))⁻¹ ^ n * α ^ n = (α + β) ^ n := by
  rw [← mul_pow]; congr 1; field_simp

/-- Brunn--Minkowski for compact sets of positive volume. -/
theorem brunn_minkowski_pos (hd : 0 < d) {A B : Set (Vec d)} (hA : IsCompact A)
    (hB : IsCompact B) (hA0 : volume A ≠ 0) (hB0 : volume B ≠ 0) :
    volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : d ≠ 0 := hd.ne'
  have hAt : volume A ≠ ∞ := hA.measure_lt_top.ne
  have hBt : volume B ≠ ∞ := hB.measure_lt_top.ne
  set a := (volume A).toReal with ha
  set b := (volume B).toReal with hb
  have hapos : 0 < a := ENNReal.toReal_pos hA0 hAt
  have hbpos : 0 < b := ENNReal.toReal_pos hB0 hBt
  have hVA : volume A = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAt).symm
  have hVB : volume B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBt).symm
  set α := a ^ ((1 : ℝ) / d) with hα_def
  set β := b ^ ((1 : ℝ) / d) with hβ_def
  have hα : 0 < α := Real.rpow_pos_of_pos hapos _
  have hβ : 0 < β := Real.rpow_pos_of_pos hbpos _
  have hαd : α ^ d = a := by rw [hα_def, one_div]; exact Real.rpow_inv_natCast_pow hapos.le hdne
  have hβd : β ^ d = b := by rw [hβ_def, one_div]; exact Real.rpow_inv_natCast_pow hbpos.le hdne
  have hc : 0 < α + β := add_pos hα hβ
  set l := α / (α + β) with hl
  have hl0 : 0 < l := div_pos hα hc
  have hl1 : l < 1 := by rw [hl, div_lt_one hc]; linarith
  have h1l : 1 - l = β / (β + α) := by rw [hl]; field_simp; ring
  have hXm : MeasurableSet (l⁻¹ • A) := hA.isClosed.measurableSet.const_smul₀ _
  have hYm : MeasurableSet ((1 - l)⁻¹ • B) := hB.isClosed.measurableSet.const_smul₀ _
  have hvolX : volume (l⁻¹ • A) = ENNReal.ofReal ((α + β) ^ d) := by
    rw [Measure.addHaar_smul, Module.finrank_fin_fun, hVA,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (pow_nonneg (inv_pos.2 hl0).le _),
      ← hαd, hl, inv_pow_mul hα hβ]
  have hvolY : volume ((1 - l)⁻¹ • B) = ENNReal.ofReal ((α + β) ^ d) := by
    rw [Measure.addHaar_smul, Module.finrank_fin_fun, hVB,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (pow_nonneg (inv_pos.2 (sub_pos.2 hl1)).le _),
      ← hβd, h1l, inv_pow_mul hβ hα, add_comm β α]
  have hABm : MeasurableSet (A + B) := (hA.add hB).isClosed.measurableSet
  have key := PrekopaLeindlerProof.ennreal_vec d hl0 hl1
    (f := (l⁻¹ • A).indicator 1) (g := ((1 - l)⁻¹ • B).indicator 1) (k := (A + B).indicator 1)
    (measurable_one.indicator hXm) (measurable_one.indicator hYm) (measurable_one.indicator hABm)
    (fun x y => by
      by_cases hx : x ∈ l⁻¹ • A
      · by_cases hy : y ∈ (1 - l)⁻¹ • B
        · have hmem : l • x + (1 - l) • y ∈ A + B := by
            obtain ⟨a', ha', rfl⟩ := hx
            obtain ⟨b', hb', rfl⟩ := hy
            refine ⟨a', ha', b', hb', ?_⟩
            rw [smul_inv_smul₀ hl0.ne', smul_inv_smul₀ (sub_pos.2 hl1).ne']
          simp [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hmem]
        · simp [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (sub_pos.2 hl1)]
      · simp [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hl0])
  rw [lintegral_indicator_one hXm, lintegral_indicator_one hYm, lintegral_indicator_one hABm,
    hvolX, hvolY, ← ENNReal.rpow_add _ _ (by simp; positivity) ENNReal.ofReal_ne_top] at key
  simp only [add_sub_cancel, ENNReal.rpow_one] at key
  have h2 : ENNReal.ofReal (α + β) ≤ volume (A + B) ^ ((1 : ℝ) / d) := by
    calc ENNReal.ofReal (α + β)
        = ENNReal.ofReal ((α + β) ^ d) ^ ((1 : ℝ) / d) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hc.le _) (by positivity), one_div,
            Real.pow_rpow_inv_natCast hc.le hdne]
      _ ≤ _ := ENNReal.rpow_le_rpow key (by positivity)
  rw [hVA, hVB, ENNReal.ofReal_rpow_of_nonneg hapos.le (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hbpos.le (by positivity), ← ENNReal.ofReal_add hα.le hβ.le]
  exact h2

end PDE.BrunnMinkowskiProof
