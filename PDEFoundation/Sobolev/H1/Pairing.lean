module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Graph

/-!
# Integrable `L²` pairings on native vector domains

This module records the `L²` membership and integrability facts used by weak
divergence-form equations.  Native vector fields retain the project's
coordinatewise `GradMemLpOn` compatibility surface; the exact Hilbert-vector
equivalence in `W1p.EuclideanGradient` shows that this is genuine Euclidean
vector-valued `L²` membership.

The explicit integrability conclusions are important: weak PDE predicates
must not rely on Lean's totalized value for a nonintegrable Bochner integral.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- Native-vector `L²` membership on `U`, as an exact specialization of the
existing coordinatewise gradient-field predicate.

By `gradMemLpOn_iff_memLp_toHilbertVecField`, this is equivalent without a
dimension-dependent factor to `L²` membership of the Euclidean Hilbert lift.
-/
abbrev MemVectorL2On {d : ℕ}
    (U : Set (Vec d)) (F : Vec d → Vec d) : Prop :=
  GradMemL2On U F

/-- The product of two scalar `L²(U)` representatives is integrable on `U`. -/
theorem integrableOn_mul_of_memL2On
    {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemL2On U f) (hg : MemL2On U g) :
    IntegrableOn (fun x => f x * g x) U := by
  simpa [MemL2On, MemLpOn, volumeOn] using!
    hf.integrable_mul hg

/-- The Euclidean dot product of two native-vector `L²(U)` representatives is
integrable on `U`. -/
theorem integrableOn_vecDot_of_memVectorL2On
    {d : ℕ} {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G) :
    IntegrableOn (fun x => vecDot (F x) (G x)) U := by
  simpa only [vecDot] using!
    integrable_finsetSum Finset.univ fun i _ =>
      integrableOn_mul_of_memL2On (hF i) (hG i)

/-- The squared Euclidean magnitude of a native-vector `L²(U)` field is
integrable on `U`. -/
theorem integrableOn_vecNormSq_of_memVectorL2On
    {d : ℕ} {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2On U F) :
    IntegrableOn (fun x => vecNormSq (F x)) U := by
  simpa only [vecNormSq] using
    integrableOn_vecDot_of_memVectorL2On hF hF

namespace WeakTestFunction

/-- The classical gradient of a bundled smooth test function, expressed in
the native-vector API. -/
noncomputable def grad {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) : Vec d → Vec d :=
  fun x i => φ.partialDeriv i x

@[simp]
theorem grad_apply {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (x : Vec d) (i : Fin d) :
    φ.grad x i = φ.partialDeriv i x :=
  rfl

/-- A bundled smooth test function belongs to scalar `L²(U)`. -/
theorem memL2On {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) :
    MemL2On U φ.toFun :=
  φ.memLp_toFun 2

/-- The classical gradient of a bundled smooth test function belongs to
native-vector `L²(U)`. -/
theorem grad_memVectorL2On {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) :
    MemVectorL2On U φ.grad := by
  intro i
  exact φ.memLp_partialDeriv i 2

end WeakTestFunction

/-- Pairing scalar `L²` data with a bundled smooth test function is genuinely
integrable. -/
theorem integrableOn_mul_weakTestFunction
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemL2On U f) (φ : WeakTestFunction U) :
    IntegrableOn (fun x => f x * φ x) U :=
  integrableOn_mul_of_memL2On hf φ.memL2On

/-- Pairing native-vector `L²` data with the gradient of a bundled smooth test
function is genuinely integrable. -/
theorem integrableOn_vecDot_weakTestFunction_grad
    {d : ℕ} {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2On U F) (φ : WeakTestFunction U) :
    IntegrableOn (fun x => vecDot (F x) (φ.grad x)) U :=
  integrableOn_vecDot_of_memVectorL2On hF φ.grad_memVectorL2On

end PDE
