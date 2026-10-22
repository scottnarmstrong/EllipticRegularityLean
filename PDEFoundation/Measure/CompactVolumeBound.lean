module

public import PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Extending compact volume bounds to open sets

Inner regularity upgrades a uniform bound on the volumes of compact subsets
to an `ℝ≥0∞` bound on the whole open set, including when finiteness is not
known in advance.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- A uniform real volume bound for every compact subset of an open set gives
the corresponding extended-real volume bound for the open set itself. -/
theorem volume_isOpen_le_of_compact_toReal_le
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {C : ℝ} (hC : 0 ≤ C)
    (hcompact : ∀ K : Set (Vec d), K ⊆ U → IsCompact K →
      (volume K).toReal ≤ C) :
    volume U ≤ ENNReal.ofReal C := by
  rw [hU.measurableSet.measure_eq_iSup_isCompact volume]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  exact (ENNReal.le_ofReal_iff_toReal_le hK.measure_ne_top hC).mpr
    (hcompact K hKU hK)

end PDE
