module

public import EllipticRegularity.Parabolic.CauchyDef

/-! # Initial-time mass identity for Cauchy solutions -/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set

/-- At the initial time, the Cauchy datum is integrable and its integral is
the slice integral. This is the endpoint case of conservation of mass. -/
theorem cauchy_mass_initial {d : ℕ} (a : ParCoeffField d) (s T : ℝ)
    (f : Vec d → ℝ) (hf : Integrable f volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) :
    Integrable (parSlice u.toFun s) volume ∧
      ∫ x, u.toFun (x, s) = ∫ x, f x := by
  have hinit : ∀ᵐ x : Vec d, u.toFun (x, s) = f x := hu.2
  refine ⟨?_, ?_⟩
  · exact hf.congr (hinit.mono fun x hx => hx.symm)
  · exact integral_congr_ae hinit

end PDE.Parabolic.Duality
