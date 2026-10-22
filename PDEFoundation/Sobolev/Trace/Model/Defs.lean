module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The half-space model for the trace theorems

The model space is `Vec n × ℝ`, a point `(x', t)`; the upper half-space is `t > 0` and its
boundary `t = 0` is identified with `Vec n`.  For `v : Vec n × ℝ → ℝ` we write `tanGrad v` for
the gradient in `x'`, `normDeriv v` for `∂ₜ v`, and `modelGradNorm v` for the Euclidean length of
the full gradient.  `flatGagliardo n q p w` is the `p`-th power of the Gagliardo seminorm on
`Vec n` with kernel exponent `q` (for the trace, `q = n + p - 1`), with the Euclidean distance.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

/-- Tangential gradient `∇' v` on the model space. -/
noncomputable def tanGrad {n : ℕ} (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) : Vec n :=
  fun i => fderiv ℝ v z (basisVec i, 0)

/-- Normal derivative `∂ₜ v` on the model space. -/
noncomputable def normDeriv {n : ℕ} (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) : ℝ :=
  fderiv ℝ v z (0, 1)

/-- Euclidean length of the full gradient `(∇' v, ∂ₜ v)`. -/
noncomputable def modelGradNorm {n : ℕ} (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) : ℝ :=
  Real.sqrt (vecNormSq (tanGrad v z) + normDeriv v z ^ 2)

/-- The open upper half-space `t > 0`. -/
def upperHalf (n : ℕ) : Set (Vec n × ℝ) := univ ×ˢ Ioi 0

/-- The closed upper half-space `t ≥ 0`. -/
def closedUpperHalf (n : ℕ) : Set (Vec n × ℝ) := univ ×ˢ Ici 0

/-- `p`-th power of the flat Gagliardo seminorm with kernel exponent `q`:
`∬ |w x' - w y'|^p / |x' - y'|^q dx' dy'` (Euclidean distance; `0/0 = 0` on the diagonal). -/
noncomputable def flatGagliardo (n : ℕ) (q p : ℝ) (w : Vec n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x', ∫⁻ y', ENNReal.ofReal (|w x' - w y'| ^ p / vecEuclideanNorm (x' - y') ^ q)

end PDE.TraceLane
