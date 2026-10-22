module

public import PDEFoundation.Ambient.VecAppend
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Volume under splitting native coordinate vectors

Literal coordinate splitting preserves volume: volume on `Vec (m + n)` is
transported to the product of volume on `Vec m` and volume on `Vec n`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

private def vecAppendMeasurableEquiv (m n : ℕ) :
    Vec (m + n) ≃ᵐ (Vec m × Vec n) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ)
      finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))

private theorem vecAppendMeasurableEquiv_apply (m n : ℕ) (x : Vec (m + n)) :
    vecAppendMeasurableEquiv m n x = vecAppendEquiv m n x := rfl

/-- Splitting native coordinates preserves the coordinate-product volume exactly. -/
theorem measurePreserving_vecAppendEquiv (m n : ℕ) :
    MeasurePreserving (vecAppendEquiv m n)
      (volume : Measure (Vec (m + n)))
      (volume : Measure (Vec m × Vec n)) := by
  have hPerm :=
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (m + n) => ℝ) finSumFinEquiv).symm
  have hSplit :=
    volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin n => ℝ)
  have h := hSplit.comp hPerm
  simpa only [volume_pi, ← vecAppendMeasurableEquiv_apply] using! h

end PDE
