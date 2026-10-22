module

public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.C1Boundary
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.W1p.Algebra
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Trace on the boundary of a `C¹` domain: definitions

Surface measure `dσ` on `∂Ω`, the `W^{1,p}` norm, the Gagliardo seminorm, the Besov norm, the
Besov class, and the trace predicate of Section 1.3 of the manuscript.

See Section 1.3 of the manuscript.
-/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

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

/-- The Gagliardo seminorm `[f]_{B^s_{p,p}(∂Ω)}` of equation (1.46), in `[0,∞]`:
`(∬ |f x - f y|^p / |x-y|^{d-1+sp} dσ dσ)^{1/p}` with the Euclidean distance `|x-y|`.  On the
diagonal the integrand is `0/0 = 0` (this matters only when `d = 1`, where `σ` has atoms). -/
noncomputable def gagliardoSeminorm {d : ℕ} (Ω : Set (Vec d)) (s p : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ x, ∫⁻ y, ENNReal.ofReal
      (|f x - f y| ^ p / vecEuclideanNorm (x - y) ^ ((d : ℝ) - 1 + s * p))
      ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω) ^ (1 / p)

/-- The Besov norm `‖f‖_{B^s_{p,p}(∂Ω)} = ‖f‖_{L^p(∂Ω)} + [f]_{B^s_{p,p}(∂Ω)}`, in `[0,∞]`. -/
noncomputable def besovNorm {d : ℕ} (Ω : Set (Vec d)) (s p : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + gagliardoSeminorm Ω s p f

/-- `f` lies in the Besov class `B^s_{p,p}(∂Ω)`: it is `σ`-measurable with finite Besov norm. -/
def IsBesov {d : ℕ} (Ω : Set (Vec d)) (s p : ℝ) (f : Vec d → ℝ) : Prop :=
  AEMeasurable f (boundarySurfaceMeasure Ω) ∧ besovNorm Ω s p f < ∞

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

end PDE
