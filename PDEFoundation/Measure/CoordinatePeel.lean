module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import PDEFoundation.Ambient.Basic

/-!
# Coordinate-peeling Fubini on native vectors

This module extracts the coordinate-peeling convention already used by
`LeanIntoHomogenization` into the common PDE foundation.  It rewrites an
integral on `Vec (n + 1)` as an iterated integral along any chosen coordinate.
The remaining coordinates retain their native `Vec n` representation.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- An integral on `Vec (n + 1)` equals the iterated integral obtained by
peeling off coordinate `i` as the inner one-dimensional integral. -/
theorem integral_peel_coord {n : ℕ} (i : Fin (n + 1))
    {f : Vec (n + 1) → ℝ}
    (hf : Integrable f (volume : Measure (Vec (n + 1)))) :
    (∫ x, f x ∂(volume : Measure (Vec (n + 1)))) =
      ∫ z : Vec n, ∫ t : ℝ, f (i.insertNth t z)
        ∂(volume : Measure ℝ) ∂(volume : Measure (Vec n)) := by
  classical
  let μ : ∀ _ : Fin (n + 1), Measure ℝ := fun _ => volume
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) i
  have hMeasurePreserving :=
    measurePreserving_piFinSuccAbove μ i
  have hvolume :
      (volume : Measure (Vec (n + 1))) = Measure.pi μ :=
    volume_pi
  have hIntegrable :
      Integrable (fun p => f (e.symm p))
        ((μ i).prod
          (Measure.pi fun j => μ (i.succAbove j))) := by
    have hPi : Integrable f (Measure.pi μ) := by
      rw [← hvolume]
      exact hf
    exact
      hMeasurePreserving.symm.integrable_comp_of_integrable hPi
  rw [hvolume,
    ← hMeasurePreserving.symm.integral_comp' f,
    integral_prod_symm _ hIntegrable]
  rfl

end

end PDE
