module

public import EllipticRegularity.Parabolic.Cauchy.Lions.InitialTrace
public import EllipticRegularity.Parabolic.Cauchy.Lions.TestMaps

/-! # Closure and representation data for the Cauchy–Lions construction

The two hypotheses `hclose`, `hrep` repeat in a large block of internal signatures.  They are
named here as reducible abbreviations of the exact propositions previously written inline, so that
the unfolded statements are unchanged and the defeq to the consumers' expectations is discharged
once.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

/-- The pair `(u, u₀)` lies in the closure of the range of the initial-trace map. -/
abbrev CauchyClosure {d : ℕ} {s T : ℝ} (u : CauchyX d s T) (u₀ : CauchyY d) : Prop :=
  WithLp.toLp 2 (u, u₀) ∈
    (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
      (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure

/-- The weak-form representation identity of `u` against the adjoint test maps, with datum `f`. -/
abbrev CauchyRepresents {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : CauchyX d s T) : Prop :=
  ∀ φ : CauchyTestSpace d s T,
    inner ℝ u (cauchyT (c := 1) ha φ) = inner ℝ (hf.toLp f) (cauchyGamma φ)

end PDE.Parabolic.Lions
