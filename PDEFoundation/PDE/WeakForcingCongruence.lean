module

public import PDEFoundation.PDE.WeakDivergenceForm

/-! # Almost-everywhere changes of divergence forcing -/

@[expose] public section

namespace PDE.IsWeakDivergenceFormSolutionOn

open MeasureTheory

/-- Changing the divergence forcing almost everywhere on the equation domain
preserves the actual weak equation and its test integrability. -/
theorem of_ae_eq_forcing
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeOn U] G)
    (hsol : IsWeakDivergenceFormSolutionOn a U u f F) :
    IsWeakDivergenceFormSolutionOn a U u f G := by
  intro φ
  obtain ⟨htest, hidentity⟩ := hsol φ
  have hpair : (fun x => vecDot (F x) (φ.grad x)) =ᵐ[volumeOn U]
      fun x => vecDot (G x) (φ.grad x) := by
    filter_upwards [hFG] with x hx
    rw [hx]
  refine ⟨⟨htest.flux_integrable, htest.source_integrable,
    (integrableOn_congr_fun_ae hpair).mp htest.forcing_integrable⟩, ?_⟩
  rw [← integral_congr_ae hpair]
  exact hidentity

end PDE.IsWeakDivergenceFormSolutionOn
