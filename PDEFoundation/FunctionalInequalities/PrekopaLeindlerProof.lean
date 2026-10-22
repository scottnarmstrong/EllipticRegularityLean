module

public import PDEFoundation.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.Induction
public import PDEFoundation.FunctionalInequalities.PrekopaLeindler.Modification

/-!
# Proof of `PDE.prekopa_leindler` (Theorem 1.2)

`PDE.PrekopaLeindlerProof.result` is the Prékopa--Leindler inequality for
nonnegative integrable functions. It is deduced from the `[0,∞]`-valued measurable version
(`ennreal_vec`, proved by induction on the dimension from the one-dimensional case, which in turn
follows from the layer-cake formula and one-dimensional Brunn--Minkowski) by replacing `f, g` by
measurable minorants and `h` by a measurable majorant, which changes no integral.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory

theorem result (d : ℕ) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : Vec d → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hyp : ∀ x y : Vec d, f x ^ l * g y ^ (1 - l) ≤ h (l • x + (1 - l) • y)) :
    (∫ x, f x) ^ l * (∫ x, g x) ^ (1 - l) ≤ ∫ x, h x := by
  have hl' : 0 < 1 - l := sub_pos.2 hl1
  obtain ⟨F, hFm, hFle, hFae⟩ := exists_measurable_le_ae_eq
    (hf.aemeasurable.ennreal_ofReal : AEMeasurable (fun x => ENNReal.ofReal (f x)) volume)
  obtain ⟨G, hGm, hGle, hGae⟩ := exists_measurable_le_ae_eq
    (hg.aemeasurable.ennreal_ofReal : AEMeasurable (fun x => ENNReal.ofReal (g x)) volume)
  obtain ⟨K, hKm, hKge, hKae⟩ := exists_measurable_ge_ae_eq
    (hh.aemeasurable.ennreal_ofReal : AEMeasurable (fun x => ENNReal.ofReal (h x)) volume)
  have key := ennreal_vec d hl0 hl1 hFm hGm hKm fun x y => by
    calc F x ^ l * G y ^ (1 - l)
        ≤ ENNReal.ofReal (f x) ^ l * ENNReal.ofReal (g y) ^ (1 - l) := by
          gcongr
          · exact hFle x
          · exact hGle y
      _ = ENNReal.ofReal (f x ^ l * g y ^ (1 - l)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) _),
            ENNReal.ofReal_rpow_of_nonneg (hf0 x) hl0.le,
            ENNReal.ofReal_rpow_of_nonneg (hg0 y) hl'.le]
      _ ≤ ENNReal.ofReal (h (l • x + (1 - l) • y)) := ENNReal.ofReal_le_ofReal (hyp x y)
      _ ≤ _ := hKge _
  rw [lintegral_congr_ae hFae, lintegral_congr_ae hGae, lintegral_congr_ae hKae,
    ← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0),
    ← ofReal_integral_eq_lintegral_ofReal hh (Filter.Eventually.of_forall hh0)] at key
  have hI : 0 ≤ ∫ x, f x := integral_nonneg fun x => hf0 x
  have hJ : 0 ≤ ∫ x, g x := integral_nonneg fun x => hg0 x
  rw [ENNReal.ofReal_rpow_of_nonneg hI hl0.le, ENNReal.ofReal_rpow_of_nonneg hJ hl'.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hI _)] at key
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => hh0 x)).1 key

end PDE.PrekopaLeindlerProof
