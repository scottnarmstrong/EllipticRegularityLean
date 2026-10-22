module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ExistenceAssembly
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.RepresentativeSolution

/-! # Closed whole-space Cauchy existence theorem -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PDE.Parabolic.Lions

/-- The Lions construction, global slice bound, and jointly measurable Riesz representative give
an energy solution for every whole-space `L²` initial datum. -/
theorem exists_cauchy_energy_solution
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d))) :
    ∃ W : ParH1Function (univ : Set (Vec d)) (Icc s T),
      IsCauchySolution a s T f W := by
  apply exists_cauchy_energy_solution_of_representative_hypothesis hsT ha f hf
  intro u u₀ hclose hrep hglobalSliceBound
  exact PDE.Parabolic.LionsRep.exists_cauchy_energy_representative
    hsT ha f hf u hclose hrep hglobalSliceBound

end PDE.Parabolic.Lions
