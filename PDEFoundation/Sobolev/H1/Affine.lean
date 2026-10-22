module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Affine

/-!
# Affine transport of representative-level `H¹`

The compatibility operations are the exact `p = 2` specializations of the
generic `W1pFunction` operations.  No second weak-derivative proof is kept in
the `H¹` layer.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE

namespace H1Function

/-- Translate an `H¹(U)` representative to `H¹(z + U)`. -/
noncomputable def translate {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (z : Vec d) :
    H1Function (translateSet z U) :=
  (u.toW1pFunction.translate z).toH1Function

@[simp]
theorem translate_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (z x : Vec d) :
    (u.translate z).toFun x = u.toFun (x - z) :=
  rfl

@[simp]
theorem translate_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (z x : Vec d) :
    (u.translate z).grad x = u.grad (x - z) :=
  rfl

/-- Push `H¹(U)` to `H¹(a • U)` by the amplitude-normalized positive
dilation `v(x) = a * u(a⁻¹ • x)`. -/
noncomputable def dilate {d : ℕ} {U : Set (Vec d)}
    {a : ℝ} (ha : 0 < a) (u : H1Function U) :
    H1Function (a • U) :=
  (u.toW1pFunction.dilate ha).toH1Function

@[simp]
theorem dilate_toFun {d : ℕ} {U : Set (Vec d)}
    {a : ℝ} (ha : 0 < a) (u : H1Function U)
    (x : Vec d) :
    (u.dilate ha).toFun x = a * u.toFun (a⁻¹ • x) :=
  rfl

@[simp]
theorem dilate_grad {d : ℕ} {U : Set (Vec d)}
    {a : ℝ} (ha : 0 < a) (u : H1Function U)
    (x : Vec d) :
    (u.dilate ha).grad x = u.grad (a⁻¹ • x) :=
  rfl

end H1Function

end PDE
