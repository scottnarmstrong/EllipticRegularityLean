module

public import EllipticRegularity.DeGiorgi.MoserIter.Hypotheses

/-!
# Adding constants preserves sub- and supersolutions

The weak formulations only involve the weak gradient, which `addConst` leaves unchanged.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.DGNMMoser

variable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} [IsFiniteMeasure (volumeOn U)]

theorem subharmonic_addConst {u : H1Function U}
    (h : IsWeakDivergenceFormSubharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSubharmonicOn a U (u.addConst c) := by
  have hg : (u.addConst c).grad = u.grad := funext fun x => H1Function.grad_addConst u c x
  intro φ hφ
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h φ hφ
  refine ⟨⟨?_, h2, h3⟩, ?_⟩
  · simpa only [hg] using h1
  · simpa only [hg] using h4

theorem superharmonic_addConst {u : H1Function U}
    (h : IsWeakDivergenceFormSuperharmonicOn a U u) (c : ℝ) :
    IsWeakDivergenceFormSuperharmonicOn a U (u.addConst c) := by
  have hg : (u.addConst c).grad = u.grad := funext fun x => H1Function.grad_addConst u c x
  intro φ hφ
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h φ hφ
  refine ⟨⟨?_, h2, h3⟩, ?_⟩
  · simpa only [hg] using h1
  · simpa only [hg] using h4

end PDE.DGNMMoser
