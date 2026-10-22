module

public import PDEFoundation.Sobolev.Mean
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The mean of a function vanishing on a set of positive density
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- If `f` vanishes on `V \ t` and `|t ∩ V| ≤ (2/3)|V|`, then
`m² |V| ≤ 3 ∫_V (f - m)²` where `m` is the mean of `f` over `V`. -/
theorem mean_sq_mul_volume_le {d : ℕ} {V t : Set (Vec d)} (hV : MeasurableSet V)
    (ht : MeasurableSet t) (hVfin : volume V < ⊤) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict V))
    (hzero : ∀ x ∈ V, x ∉ t → f x = 0)
    (htV : volume (t ∩ V) ≤ ENNReal.ofReal (2 / 3) * volume V) :
    (integralAverage V f) ^ 2 * (volume V).toReal ≤
      3 * ∫ x in V, (f x - integralAverage V f) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVfin⟩
  set m := integralAverage V f with hm
  set E := V \ t with hE
  have hEmeas : MeasurableSet E := hV.diff ht
  have hint : IntegrableOn (fun x => (f x - m) ^ 2) V volume := by
    have : MemLp (fun x => f x - m) 2 (volume.restrict V) := hf.sub (memLp_const _)
    exact this.integrable_sq
  have h1 : ∫ x in E, (f x - m) ^ 2 ≤ ∫ x in V, (f x - m) ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall Set.sdiff_subset)
  have h2 : ∫ x in E, (f x - m) ^ 2 = m ^ 2 * (volume E).toReal := by
    rw [setIntegral_congr_fun hEmeas (g := fun _ => m ^ 2)]
    · simp [Measure.real, mul_comm]
    · intro x hx
      simp [hzero x hx.1 hx.2]
  have h3 : (volume V).toReal ≤ 3 * (volume E).toReal := by
    have hsum : volume (V ∩ t) + volume E = volume V := measure_inter_add_sdiff V ht
    have hne : volume (V ∩ t) ≠ ⊤ := ne_top_of_le_ne_top hVfin.ne (measure_mono Set.inter_subset_left)
    have hEne : volume E ≠ ⊤ := ne_top_of_le_ne_top hVfin.ne (measure_mono Set.sdiff_subset)
    have hreal : (volume (V ∩ t)).toReal + (volume E).toReal = (volume V).toReal := by
      rw [← ENNReal.toReal_add hne hEne, hsum]
    have hle : (volume (V ∩ t)).toReal ≤ 2 / 3 * (volume V).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin.ne)
        (by rwa [Set.inter_comm] : volume (V ∩ t) ≤ _)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at this
    linarith
  calc m ^ 2 * (volume V).toReal ≤ m ^ 2 * (3 * (volume E).toReal) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = 3 * (m ^ 2 * (volume E).toReal) := by ring
    _ ≤ 3 * ∫ x in V, (f x - m) ^ 2 := by rw [← h2]; linarith

end PDE.DGNMLog
