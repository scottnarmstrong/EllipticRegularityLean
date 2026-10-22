module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassApproximation
public import EllipticRegularity.Parabolic.Cauchy.Duality.MassLionsExistence

@[expose] public section

set_option autoImplicit false

namespace PDE.Parabolic.Duality

open MeasureTheory Set

/-- Mass conservation for general `L¹ ∩ L²` data, using compactly supported datum truncations,
the Lions existence construction, compact-data exponential flux bounds, and `L¹` contraction. -/
theorem cauchy_mass_l1_l2_core (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (t : ℝ) (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧
      ∫ x, u.toFun (x, t) = ∫ x, f x := by
  classical
  let fn : ℕ → Vec d → ℝ := cauchyMassDataCutoff f
  have htruncate := cauchyMassDataCutoff_properties f hf1 hf2
  have hexists : ∀ n, ∃ v : ParH1Function (univ : Set (Vec d)) (Icc s T),
      IsCauchySolution a s T (fn n) v := by
    intro n
    exact exists_cauchy_solution_from_lions hsT ha (fn n) (by
      simpa [fn] using htruncate.2.1 n)
  choose vn hvn using hexists
  apply cauchy_mass_of_ball_supported_approximations hsT ha f hf1 hf2 u hu fn vn
    htruncate.1 htruncate.2.1 ?_ hvn ?_ ht
  · intro n
    simpa [fn] using htruncate.2.2.1 n
  · simpa [fn] using htruncate.2.2.2

end PDE.Parabolic.Duality
