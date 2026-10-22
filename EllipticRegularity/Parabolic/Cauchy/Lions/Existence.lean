module

public import EllipticRegularity.Parabolic.Cauchy.Lions.Coercivity
public import EllipticRegularity.Parabolic.Cauchy.Lions.InitialTrace

/-! # The Lions Cauchy pair -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

/-- The damped Lions representation packages a space-time value/gradient pair and its initial
trace in the closure of the joint graph of compactly supported Cauchy tests. -/
theorem exists_cauchy_lions_pair {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d))) :
    ∃ u : CauchyX d s T, ∃ u₀ : CauchyY d,
      WithLp.toLp 2 (u, u₀) ∈
        (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
          (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure ∧
      ∀ φ : CauchyTestSpace d s T,
        inner ℝ u (cauchyT (c := 1) ha φ) =
          inner ℝ (hf.toLp f) (cauchyGamma φ) := by
  obtain ⟨hα, hcoer⟩ := cauchy_coercivity hsT ha
  exact lions_representation_initial_trace_components
    (cauchyJ (d := d) (s := s) (T := T)) (cauchyT (c := 1) ha) (cauchyGamma (d := d) (s := s) (T := T))
    hα hcoer (hf.toLp f)

end PDE.Parabolic.Lions
