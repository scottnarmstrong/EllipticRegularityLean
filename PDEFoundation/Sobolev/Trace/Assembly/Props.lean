module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Sobolev.Trace.Model.Defs

/-!
# Interface statements of the trace development

These are the statements of separately proved theorems of the trace development, recorded as propositions so
that the assembly can be written against them:

* `ModelTraceLp n p`, `ModelTraceGagliardo n p`: the half-space trace bounds (manuscript Steps 1-3);
* `SmoothTraceBound Ω p`: the trace bound for `C¹(Ω̄)` functions (manuscript Step 4);
* `DensityProp Ω p`: density of globally `C¹` functions in `W^{1,p}(Ω)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

/-- Manuscript Step 1 on the half-space. -/
def ModelTraceLp (n : ℕ) (p : ℝ) : Prop :=
  ∀ v : Vec n × ℝ → ℝ, ContDiffOn ℝ 1 v (closedUpperHalf n) →
    (∃ K, IsCompact K ∧ ∀ z ∉ K, v z = 0) →
    ∫⁻ x', ENNReal.ofReal (|v (x', 0)| ^ p) ≤
      ENNReal.ofReal p * (∫⁻ z in upperHalf n, ENNReal.ofReal (|v z| ^ p)) ^ ((p - 1) / p) *
        (∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv v z| ^ p)) ^ (1 / p)

/-- Manuscript Steps 2-3 on the half-space. -/
def ModelTraceGagliardo (n : ℕ) (p : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ v : Vec n × ℝ → ℝ, ContDiffOn ℝ 1 v (closedUpperHalf n) →
    (∃ K, IsCompact K ∧ ∀ z ∉ K, v z = 0) →
    flatGagliardo n (n + p - 1) p (fun x' => v (x', 0)) ≤
      (C : ℝ≥0∞) * ∫⁻ z in upperHalf n, ENNReal.ofReal (modelGradNorm v z ^ p)

/-- Manuscript Step 4: the trace bound for `C¹(Ω̄)` functions. -/
def SmoothTraceBound {d : ℕ} (Ω : Set (Vec d)) (p : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ φ : Vec d → ℝ, ContDiffOn ℝ 1 φ (closure Ω) →
    eLpNorm φ (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p φ (classicalGradient φ) ∧
      gagliardoSeminorm Ω (1 - 1 / p) p φ ≤ (C : ℝ≥0∞) * w1pPairNorm Ω p φ (classicalGradient φ)

/-- Density of globally `C¹` functions in `W^{1,p}(Ω)`. -/
def DensityProp {d : ℕ} (Ω : Set (Vec d)) (p : ℝ) : Prop :=
  ∀ u : W1pFunction Ω (ENNReal.ofReal p), ∃ φ : ℕ → Vec d → ℝ, (∀ k, ContDiff ℝ 1 (φ k)) ∧
    Tendsto (fun k => w1pPairNorm Ω p (φ k - u.toFun) (classicalGradient (φ k) - u.grad))
      atTop (𝓝 0)

end PDE.TraceLane
