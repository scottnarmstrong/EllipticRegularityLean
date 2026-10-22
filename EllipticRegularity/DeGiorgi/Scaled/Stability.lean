module

public import EllipticRegularity.DeGiorgi.Holder.Interface
public import PDEFoundation.PDE.DGNM.Scaling

/-!
# Stability of solutions under translation and dilation

The hypothesis `ScaleStability` of the De Giorgi Hölder theorem, proved from the
change of variables `blowUp` of `PDEFoundation.PDE.DGNM.Scaling`.
-/

@[expose] public section

namespace PDE.DGNMScaled

open PDE MeasureTheory

/-- Solutions on `B_1` are stable under `u ↦ u(x₀ + ρ ·)` for `B_ρ(x₀) ⊆ B_1`
(the coefficient field becomes `a(x₀ + ρ ·)`, with the same ellipticity contrast). -/
theorem scaleStability (d : ℕ) : PDE.DGNMHolder.ScaleStability d := by
  intro Λ a ha hEll u hsol x₀ ρ hρ hball
  refine ⟨DGNM.blowUpCoeff a x₀ ρ, DGNM.blowUp u x₀ hρ hball,
    DGNM.blowUpCoeff_aemeasurable ha x₀ hρ hball, DGNM.blowUpCoeff_elliptic hEll x₀ hρ hball,
    DGNM.solutionOn_blowUp (isOpen_euclideanBall _ _) hsol x₀ hρ hball, ?_⟩
  filter_upwards with y
  exact DGNM.blowUp_toFun u x₀ hρ hball y

end PDE.DGNMScaled
