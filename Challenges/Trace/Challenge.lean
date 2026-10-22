module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The trace inequality

Challenge: the trace operator `W^{1,p}(Ω) → B^{1-1/p}_{p,p}(∂Ω)` for a bounded connected open set
`Ω ⊆ ℝ^d` with `C¹` boundary, `1 < p < ∞`.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean norm and balls are defined below (the norm inherited by `Vec d` from Mathlib is the
supremum norm, and `Metric.ball` is never used).  Surface measure on `∂Ω` is the Euclidean
Hausdorff measure `μHE[d-1]`, taken on `HilbertVec d`, the same space with the Euclidean norm.
Sobolev functions are bundled together with chosen representatives of the function and of its
weak gradient.
-/

@[expose] public section

open scoped BigOperators ENNReal Topology

namespace PDE

open MeasureTheory Filter
open scoped NNReal

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ


/-- The Euclidean dot product on `Vec d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i


/-- The square of the Euclidean norm on `Vec d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x


/-- The Euclidean norm on `Vec d`. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)


/-- The `i`th coordinate basis vector. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)


/-- Euclidean squared distance on `Vec d`. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)


/-- The round Euclidean open ball of centre `x₀` and radius `R`. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}


/-- Lebesgue volume restricted to a domain `U`. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U


/-- The Euclidean space `ℝ^d` as a `PiLp 2` space, on which Hausdorff measure and sphere measure
are taken. -/
abbrev HilbertVec (d : ℕ) :=
  PiLp 2 (fun _ : Fin d => ℝ)

/-- Put a vector of `Vec d` into `HilbertVec d`. -/
def Vec.toHilbertVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x

/-- Return a Euclidean (Hilbert) vector to the coordinate carrier `Vec d`. -/
def HilbertVec.toVec {d : ℕ} (x : HilbertVec d) : Vec d :=
  WithLp.ofLp x


section C1Boundary

-- Keep the instance path used for `ContDiff ℝ 1 φ` and `fderiv ℝ φ y` on `Vec d` independent of
-- the inner-product-space imports needed for `HilbertVec` (both paths are definitionally equal).
attribute [-instance] InnerProductSpace.toNormedSpace

/-- `E` has `C¹` boundary: near every boundary point, `E` is the strict sublevel set `{φ < 0}`
of a `C¹` function with nowhere-vanishing derivative (equivalently, locally the open epigraph of a
`C¹` graph in rotated coordinates). -/
def HasC1Boundary {d : ℕ} (E : Set (Vec d)) : Prop :=
  ∀ x ∈ frontier E, ∃ W : Set (Vec d), IsOpen W ∧ x ∈ W ∧
    ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ y ∈ W, fderiv ℝ φ y ≠ 0) ∧
      E ∩ W = {y | y ∈ W ∧ φ y < 0}

end C1Boundary


/-- Scalar `L^p` membership on a domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)


/-- Coordinatewise `L^p` membership of a vector field on a domain. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)


/-- `gi` is the `i`th weak derivative of `u` on `U`. -/
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

/-- `Du` is a (coordinatewise) weak gradient of `u` on `U`. -/
def HasWeakGradientOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)


/-- An element of `W^{1,p}(U)`: a concrete scalar representative `toFun` and a chosen weak
gradient `grad`, both in `L^p(U)`. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad


/-- The coordinate gradient of a scalar function, expressed in the native vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)


/-- The surface measure `dσ` on `∂Ω`, as a measure on `Vec d`: the Euclidean Hausdorff measure
`H^{d-1} = μHE[d-1]` of the Euclidean realisation `HilbertVec d`, restricted to the image of
`frontier Ω`, and pulled back along the measurable equivalence `Vec d ≃ HilbertVec d`.  It is
supported on `frontier Ω`. -/
noncomputable def boundarySurfaceMeasure {d : ℕ} (Ω : Set (Vec d)) : Measure (Vec d) :=
  Measure.map HilbertVec.toVec
    ((μHE[d - 1] : Measure (HilbertVec d)).restrict (Vec.toHilbertVec '' frontier Ω))

/-- The `W^{1,p}` norm of a value/gradient pair on `Ω`:
`‖v‖_{L^p(Ω)} + ‖ |G| ‖_{L^p(Ω)}` with the Euclidean length `|G|`, in `[0,∞]`. -/
noncomputable def w1pPairNorm {d : ℕ} (Ω : Set (Vec d)) (p : ℝ) (v : Vec d → ℝ)
    (G : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNorm v (ENNReal.ofReal p) (volumeOn Ω) +
    eLpNorm (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) (volumeOn Ω)

/-- `‖u‖_{W^{1,p}(Ω)} = ‖u‖_{L^p(Ω)} + ‖∇u‖_{L^p(Ω)}`, in `[0,∞]` (finite for every `u`). -/
noncomputable def w1pNorm {d : ℕ} (Ω : Set (Vec d)) (p : ℝ)
    (u : W1pFunction Ω (ENNReal.ofReal p)) : ℝ≥0∞ :=
  w1pPairNorm Ω p u.toFun u.grad

/-- The Gagliardo seminorm `[f]_{B^s_{p,p}(∂Ω)}`, in `[0,∞]`:
`(∬ |f x - f y|^p / |x-y|^{d-1+sp} dσ dσ)^{1/p}` with the Euclidean distance `|x-y|`.  On the
diagonal the integrand is `0/0 = 0` (this matters only when `d = 1`, where `σ` has atoms). -/
noncomputable def gagliardoSeminorm {d : ℕ} (Ω : Set (Vec d)) (s p : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ∫⁻ y, ENNReal.ofReal
      (|f x - f y| ^ p / vecEuclideanNorm (x - y) ^ ((d : ℝ) - 1 + s * p))
      ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω) ^ (1 / p)

/-- The Besov norm `‖f‖_{B^s_{p,p}(∂Ω)} = ‖f‖_{L^p(∂Ω)} + [f]_{B^s_{p,p}(∂Ω)}`, in `[0,∞]`. -/
noncomputable def besovNorm {d : ℕ} (Ω : Set (Vec d)) (s p : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + gagliardoSeminorm Ω s p f

/-- `g` is a trace of `u ∈ W^{1,p}(Ω)` on `∂Ω`: `g ∈ L^p(∂Ω,dσ)` and there are
`φₙ ∈ C¹(Ω̄)` with `φₙ → u` in `W^{1,p}(Ω)` and `φₙ|_{∂Ω} → g` in `L^p(∂Ω)`. -/
def IsTraceOf {d : ℕ} (Ω : Set (Vec d)) (p : ℝ) (u : W1pFunction Ω (ENNReal.ofReal p))
    (g : Vec d → ℝ) : Prop :=
  MemLp g (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ∧
  ∃ φ : ℕ → Vec d → ℝ, (∀ n, ContDiffOn ℝ 1 (φ n) (closure Ω)) ∧
    Tendsto (fun n => w1pPairNorm Ω p (φ n - u.toFun) (classicalGradient (φ n) - u.grad))
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (φ n - g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω))
      atTop (𝓝 0)


/-- Trace inequality (Theorem 1.23).  Let `Ω ⊆ ℝ^d` be a bounded, connected, open set with `C¹`
boundary and `1 < p < ∞`.  There is a constant `C` such that every `u ∈ W^{1,p}(Ω)` has a trace
`g` on `∂Ω` (a limit in `L^p(∂Ω)` of restrictions of `C¹(Ω̄)` functions converging to `u` in
`W^{1,p}(Ω)`), the trace is unique `σ`-almost everywhere, and
`‖g‖_{B^{1-1/p}_{p,p}(∂Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}`. -/
theorem trace_inequality (d : ℕ) (hd : 1 ≤ d) (Ω : Set (Vec d))
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ : HasC1Boundary Ω) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W1pFunction Ω (ENNReal.ofReal p),
      (∃ g, IsTraceOf Ω p u g) ∧
      (∀ g g', IsTraceOf Ω p u g → IsTraceOf Ω p u g' →
        g =ᵐ[boundarySurfaceMeasure Ω] g') ∧
      ∀ g, IsTraceOf Ω p u g →
        besovNorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u := by
  sorry

end PDE
