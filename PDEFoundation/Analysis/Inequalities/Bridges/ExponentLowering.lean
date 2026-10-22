module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Measure.BallVolume

/-!
# Lowering the Sobolev exponent on finite-measure sets

`W^{1,p}(U) ⊆ W^{1,q}(U)` for `q ≤ p` when `U` has finite volume; in particular
`H¹(U) ⊆ W^{1,q}(U)` for `1 ≤ q ≤ 2`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PDE
namespace Ch1Bridges

/-- Lower the exponent of a representative-level `W^{1,p}` function on a set of finite volume. -/
def W1pFunction.lower {d : ℕ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {p q : ℝ≥0∞} (hqp : q ≤ p) (u : W1pFunction U p) : W1pFunction U q :=
  haveI : Fact (volume U < ⊤) := ⟨lt_top_iff_ne_top.mpr hU⟩
  { toFun := u.toFun
    grad := u.grad
    memLp := u.memLp.mono_exponent hqp
    gradMemLp := fun i => (u.gradMemLp i).mono_exponent hqp
    hasWeakGradient := u.hasWeakGradient }

@[simp] theorem W1pFunction.lower_toFun {d : ℕ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {p q : ℝ≥0∞} (hqp : q ≤ p) (u : W1pFunction U p) : (W1pFunction.lower hU hqp u).toFun = u.toFun :=
  rfl

@[simp] theorem W1pFunction.lower_grad {d : ℕ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {p q : ℝ≥0∞} (hqp : q ≤ p) (u : W1pFunction U p) : (W1pFunction.lower hU hqp u).grad = u.grad :=
  rfl

/-- `H¹(U) ⊆ W^{1,q}(U)` for `q ≤ 2` on a set of finite volume. -/
def H1Function.toW1p {d : ℕ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {q : ℝ≥0∞} (hq : q ≤ 2) (u : H1Function U) : W1pFunction U q :=
  W1pFunction.lower hU hq u.toW1pFunction

@[simp] theorem H1Function.toW1p_toFun {d : ℕ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {q : ℝ≥0∞} (hq : q ≤ 2) (u : H1Function U) : (H1Function.toW1p hU hq u).toFun = u.toFun :=
  rfl

@[simp] theorem H1Function.toW1p_grad {d : ℕ} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {q : ℝ≥0∞} (hq : q ≤ 2) (u : H1Function U) : (H1Function.toW1p hU hq u).grad = u.grad :=
  rfl

end Ch1Bridges
end PDE
