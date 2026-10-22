module

public import PDEFoundation.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import PDEFoundation.FunctionalInequalities.BrunnMinkowski.Core

/-!
# Proof of `PDE.brunn_minkowski` (Theorem 1.3)

`PDE.BrunnMinkowskiProof.result` is the Brunn--Minkowski inequality for
nonempty compact sets. The case of two positive volumes is deduced from the Prékopa--Leindler
inequality (`PDE.PrekopaLeindlerProof.ennreal_vec`), as in the manuscript; if a volume vanishes,
the inequality follows from translation invariance.
-/

@[expose] public section

namespace PDE.BrunnMinkowskiProof

open MeasureTheory
open scoped ENNReal Pointwise

theorem result (d : ℕ) (hd : 0 < d) (A B : Set (Vec d))
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A ^ ((1 : ℝ) / d) + volume B ^ ((1 : ℝ) / d) ≤ volume (A + B) ^ ((1 : ℝ) / d) := by
  have hdr : (0 : ℝ) < (1 : ℝ) / d := by positivity
  obtain ⟨a0, ha0⟩ := hAne
  obtain ⟨b0, hb0⟩ := hBne
  by_cases hA0 : volume A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos hdr, zero_add]
    exact ENNReal.rpow_le_rpow (volume_le_add_left ha0) hdr.le
  by_cases hB0 : volume B = 0
  · rw [hB0, ENNReal.zero_rpow_of_pos hdr, add_zero]
    exact ENNReal.rpow_le_rpow (volume_le_add_right hb0) hdr.le
  exact brunn_minkowski_pos hd hA hB hA0 hB0

end PDE.BrunnMinkowskiProof
