module

public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Sobolev.W1p.Basic

/-!
# Local representative-level `W^{1,p}`

The public local Sobolev predicate is quantified over open sets whose closure
is compact and contained in the ambient domain. On each such set it asks for
a concrete `W1pFunction` whose value representative agrees almost everywhere
with the given function.

This is the single canonical compact-containment formulation. Specialized
ball and cube lemmas below are interfaces to it, not competing definitions.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- A concrete function belongs to local `W^{1,p}` on `U` when every open
`V` with compact closure contained in `U` admits a representative-level
Sobolev function agreeing with it almost everywhere on `V`. -/
def W1pLoc {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (u : Vec d → ℝ) : Prop :=
  ∀ V : Set (Vec d), IsOpen V → IsCompact (closure V) →
    closure V ⊆ U →
      ∃ v : W1pFunction V p, v.toFun =ᵐ[volumeOn V] u

namespace W1pFunction

/-- A global representative-level Sobolev function is locally Sobolev on the
same domain. The local witnesses are its restrictions. -/
theorem w1pLoc {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) :
    W1pLoc U p u.toFun := by
  intro V hVOpen _hVCompact hVU
  refine
    ⟨u.restrict hVOpen (subset_closure.trans hVU), ?_⟩
  exact Filter.Eventually.of_forall fun _ => rfl

end W1pFunction

namespace MemW1p

/-- Representative-level global `W^{1,p}` membership implies local
membership. -/
theorem w1pLoc {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemW1p U p u) :
    W1pLoc U p u := by
  rcases hu with ⟨v, rfl⟩
  exact v.w1pLoc

end MemW1p

namespace W1pLoc

/-- Extract a representative-level Sobolev witness on an open,
compactly-contained set. -/
theorem exists_w1pFunction {d : ℕ} {U V : Set (Vec d)}
    {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : W1pLoc U p u) (hVOpen : IsOpen V)
    (hVCompact : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ v : W1pFunction V p, v.toFun =ᵐ[volumeOn V] u :=
  hu V hVOpen hVCompact hVU

/-- On native finite-dimensional vectors, boundedness supplies the compact
closure required by `W1pLoc`. -/
theorem exists_w1pFunction_of_isBounded
    {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : W1pLoc U p u)
    (hVOpen : IsOpen V) (hVBounded : Bornology.IsBounded V)
    (hVU : closure V ⊆ U) :
    ∃ v : W1pFunction V p, v.toFun =ᵐ[volumeOn V] u :=
  hu.exists_w1pFunction hVOpen hVBounded.isCompact_closure hVU

/-- Local Sobolev membership is monotone in the ambient domain. -/
theorem mono {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : W1pLoc U p u) (hVU : V ⊆ U) :
    W1pLoc V p u := by
  intro W hWOpen hWCompact hWV
  exact hu W hWOpen hWCompact (hWV.trans hVU)

/-- Restrict local Sobolev membership to a smaller domain. This is an alias
of the stronger set-monotonicity theorem and does not require the smaller
domain itself to be open. -/
theorem restrict {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : W1pLoc U p u) (hVU : V ⊆ U) :
    W1pLoc V p u :=
  hu.mono hVU

/-- Local Sobolev membership depends only on the restricted-volume a.e.
class of the value representative. -/
theorem congr_ae {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u v : Vec d → ℝ} (hu : W1pLoc U p u)
    (huv : u =ᵐ[volumeOn U] v) :
    W1pLoc U p v := by
  intro V hVOpen hVCompact hVU
  rcases hu V hVOpen hVCompact hVU with ⟨w, hwu⟩
  refine ⟨w, hwu.trans ?_⟩
  exact huv.filter_mono <| ae_mono <|
    Measure.restrict_mono_set volume (subset_closure.trans hVU)

/-- A.e.-equal value representatives have equivalent local Sobolev
membership. -/
theorem congr_ae_iff {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u v : Vec d → ℝ} (huv : u =ᵐ[volumeOn U] v) :
    W1pLoc U p u ↔ W1pLoc U p v :=
  ⟨fun hu => hu.congr_ae huv, fun hv => hv.congr_ae huv.symm⟩

/-- Extract a local Sobolev representative on a round open ball whose
corresponding round closed ball lies in the ambient domain. -/
theorem exists_euclideanBall {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {u : Vec d → ℝ} (hu : W1pLoc U p u)
    {x₀ : Vec d} {R : ℝ} (hR : 0 < R)
    (hsub : euclideanClosedBall x₀ R ⊆ U) :
    ∃ v : W1pFunction (euclideanBall x₀ R) p,
      v.toFun =ᵐ[volumeOn (euclideanBall x₀ R)] u := by
  apply hu.exists_w1pFunction
      (isOpen_euclideanBall x₀ R)
      (Bornology.IsBounded.isCompact_closure <|
        IsBoundedDomain.isBounded
          (isOpenBoundedConvexDomain_euclideanBall x₀ hR).isBoundedDomain)
  exact
    (closure_minimal
      (euclideanBall_subset_euclideanClosedBall x₀ R)
      (isClosed_euclideanClosedBall x₀ R)).trans hsub

/-- Extract a local Sobolev representative on an axis-aligned open cube with
compact closure contained in the ambient domain. -/
theorem exists_axisCube {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {u : Vec d → ℝ} (hu : W1pLoc U p u)
    (z : Vec d) (L : ℝ) (hsub : closure (axisCube z L) ⊆ U) :
    ∃ v : W1pFunction (axisCube z L) p,
      v.toFun =ᵐ[volumeOn (axisCube z L)] u :=
  hu.exists_w1pFunction
    (isOpen_axisCube z L)
    ((isBoundedDomain_axisCube z L).isBounded.isCompact_closure)
    hsub

end W1pLoc

end PDE
