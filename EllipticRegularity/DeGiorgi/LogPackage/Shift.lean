module

public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Sobolev.H1.Mean
public import PDEFoundation.Measure.BallVolume

/-!
# Adding a constant to a supersolution
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- Adding a constant does not change the chosen gradient, hence preserves supersolutions. -/
theorem superharmonic_addConst {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeOn U)]
    {a : CoeffField d} {u : H1Function U}
    (hu : IsWeakDivergenceFormSuperharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSuperharmonicOn a U (u.addConst c) := by
  intro φ hφ
  have h := hu φ hφ
  refine ⟨⟨?_, h.1.source_integrable, h.1.forcing_integrable⟩, ?_⟩
  · simpa only [H1Function.grad_addConst] using h.1.flux_integrable
  · simpa only [H1Function.grad_addConst] using h.2

/-- Adding a constant does not change the chosen gradient, hence preserves subsolutions. -/
theorem subharmonic_addConst {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeOn U)]
    {a : CoeffField d} {u : H1Function U}
    (hu : IsWeakDivergenceFormSubharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U (u.addConst c) := by
  intro φ hφ
  have h := hu φ hφ
  refine ⟨⟨?_, h.1.source_integrable, h.1.forcing_integrable⟩, ?_⟩
  · simpa only [H1Function.grad_addConst] using h.1.flux_integrable
  · simpa only [H1Function.grad_addConst] using h.2

end PDE.DGNMLog
