module

public import EllipticRegularity.Parabolic.CauchyDef

/-!
# Time reversal and transposition of parabolic coefficients

The map `(x, τ) ↦ (x, c - τ)` preserves the restricted space-time measure on
`ℝ^d × [s,T]` when `c = s + T`.  This lets the almost-everywhere ellipticity
condition pass to the reflected transposed coefficient field.
-/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set

/-- Reflection of time about the midpoint of `[s,T]` preserves null sets on the
restricted space-time slab. -/
theorem time_reflection_quasi_measure_preserving (d : ℕ) (s T : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : Vec d × ℝ => (z.1, s + T - z.2))
      (volume.restrict (univ ×ˢ Icc s T))
      (volume.restrict (univ ×ˢ Icc s T)) := by
  let ρ : ℝ → ℝ := fun τ => s + T - τ
  have hneg : MeasurePreserving (fun τ : ℝ => -τ) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg volume
  have hadd : MeasurePreserving (fun τ : ℝ => (s + T) + τ) volume volume :=
    MeasureTheory.measurePreserving_add_left volume (s + T)
  have htime : MeasurePreserving ρ volume volume := by
    convert hadd.comp hneg using 1
    ext τ
    simp [ρ, sub_eq_add_neg, add_assoc]
  have hprod : MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, ρ z.2))
      ((volume : Measure (Vec d)).prod volume)
      ((volume : Measure (Vec d)).prod volume) := by
    convert (MeasurePreserving.id (volume : Measure (Vec d))).prod htime using 1
    rfl
  have hfull : MeasurePreserving
      (fun z : Vec d × ℝ => (z.1, s + T - z.2)) volume volume := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hprod
  have hmaps : MapsTo (fun z : Vec d × ℝ => (z.1, s + T - z.2))
      (univ ×ˢ Icc s T) (univ ×ˢ Icc s T) := by
    rintro ⟨x, τ⟩ ⟨-, hτ⟩
    refine ⟨mem_univ _, ?_⟩
    rw [mem_Icc] at hτ ⊢
    constructor <;> dsimp <;> linarith
  exact hfull.quasiMeasurePreserving.restrict hmaps

end PDE.Parabolic.Duality

namespace PDE

open MeasureTheory Set

/-- Time reversal and transposition preserve `IsParabolicCoeff` on the closed
slab `[s,T]`. -/
theorem parAdjCoeff_isParabolicCoeff_core (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) :
    IsParabolicCoeff lam Lam (parAdjCoeff a (s + T)) univ (Icc s T) := by
  let ρ : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, s + T - z.2)
  have hρ := PDE.Parabolic.Duality.time_reflection_quasi_measure_preserving d s T
  refine ⟨?_, ?_⟩
  · intro i j
    have hcomp := (ha.measurable j i).mono_ac hρ.absolutelyContinuous |>.comp_aemeasurable
      hρ.aemeasurable
    simpa [Function.comp_def, parAdjCoeff, matTranspose, Matrix.transpose_apply] using hcomp
  · filter_upwards [hρ.ae ha.elliptic] with z hz
    simpa [parAdjCoeff, matTranspose] using isEllipticMatrix_transpose hz

end PDE
