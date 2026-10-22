module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Smooth

/-!
# Smooth functions as representative-level `H¹` functions

This file provides the `p = 2` facade for the bounded-domain smooth
constructors in `PDEFoundation.Sobolev.W1p.Smooth`. The value and classical
gradient representatives are transported exactly through
`W1pFunction.toH1Function`; no analytic argument is repeated here.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace H1Function

/-- Package a globally `C¹` function as an `H¹` representative on a bounded
measurable domain. -/
noncomputable def ofContDiffOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) : H1Function U :=
  (W1pFunction.ofContDiffOnIsSobolevRegularDomain
    (p := (2 : ℝ≥0∞)) hU hf).toH1Function

@[simp]
theorem ofContDiffOnIsSobolevRegularDomain_toFun
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (ofContDiffOnIsSobolevRegularDomain hU hf).toFun = f :=
  rfl

@[simp]
theorem ofContDiffOnIsSobolevRegularDomain_grad
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (ofContDiffOnIsSobolevRegularDomain hU hf).grad =
      classicalGradient f :=
  rfl

/-- Package a globally `C¹` function as an `H¹` representative on a bounded
open convex domain. -/
noncomputable def ofContDiffOnIsOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) : H1Function U :=
  (W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
    (p := (2 : ℝ≥0∞)) hU hf).toH1Function

@[simp]
theorem ofContDiffOnIsOpenBoundedConvexDomain_toFun
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (ofContDiffOnIsOpenBoundedConvexDomain hU hf).toFun = f :=
  rfl

@[simp]
theorem ofContDiffOnIsOpenBoundedConvexDomain_grad
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (ofContDiffOnIsOpenBoundedConvexDomain hU hf).grad =
      classicalGradient f :=
  rfl

end H1Function

end PDE
