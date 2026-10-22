module

public import PDEFoundation.Sobolev.Trace.Assembly.Props
public import PDEFoundation.Sobolev.Trace.Chart.Defs
public import PDEFoundation.Sobolev.Trace.Density.Chart
public import PDEFoundation.Sobolev.Trace.Density.Piece

/-!
# Approximable `W^{1,p}` functions and the pieces of a trace atlas

`ApproxW1p u` says that `u ∈ W^{1,p}(Ω)` is a `W^{1,p}(Ω)`-limit of smooth functions.  The
predicate is closed under finite sums, and it holds for a function that vanishes off a chart
cylinder of the atlas (boundary pieces) or on the open set `V` where the partition of unity sums
to one (interior piece).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal

variable {d : ℕ}

/-- `u` is the `W^{1,p}(Ω)`-limit of smooth functions. -/
def ApproxW1p (Ω : Set (Vec d)) (p : ℝ) (u : W1pFunction Ω (ENNReal.ofReal p)) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
    w1pPairNorm Ω p (φ - u.toFun) (classicalGradient φ - u.grad) < ε

theorem classicalGradient_add_of_contDiff {φ ψ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : classicalGradient (φ + ψ) = classicalGradient φ +
      classicalGradient ψ := by
  funext x i
  have h1 : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
  have : (φ + ψ) = fun y => φ y + ψ y := rfl
  simp only [classicalGradient, Pi.add_apply]
  rw [fderiv_add h1 h2]
  simp

theorem ApproxW1p.zero (Ω : Set (Vec d)) (p : ℝ) :
    ApproxW1p Ω p (0 : W1pFunction Ω (ENNReal.ofReal p)) := by
  intro ε hε
  refine ⟨0, contDiff_const, ?_⟩
  have : classicalGradient (0 : Vec d → ℝ) = 0 := by
    funext x i; simp [classicalGradient]
  have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
  simpa [w1pPairNorm, this, h0] using hε

theorem ApproxW1p.add {Ω : Set (Vec d)} {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {u v : W1pFunction Ω (ENNReal.ofReal p)}
    (hu : ApproxW1p Ω p u) (hv : ApproxW1p Ω p v) : ApproxW1p Ω p (u + v) := by
  intro ε hε
  have hεh : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨φ, hφ, hφlt⟩ := hu _ hεh
  obtain ⟨ψ, hψ, hψlt⟩ := hv _ hεh
  refine ⟨φ + ψ, hφ.add hψ, ?_⟩
  have hmeas : ∀ (φ : Vec d → ℝ) (w : W1pFunction Ω (ENNReal.ofReal p)),
      ContDiff ℝ (⊤ : ℕ∞) φ → AEStronglyMeasurable (classicalGradient φ - w.grad) (volumeOn Ω) :=
    fun φ w hφ => by
      refine aestronglyMeasurable_of_coords fun i => ?_
      exact ((continuous_classicalGradient_apply hφ i).aestronglyMeasurable).sub
        ((w.gradMemLp i).aestronglyMeasurable)
  have e1 : φ + ψ - (u + v).toFun = (φ - u.toFun) + (ψ - v.toFun) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply, W1pFunction.add_toFun]; ring
  have e2 : classicalGradient (φ + ψ) - (u + v).grad =
      (classicalGradient φ - u.grad) + (classicalGradient ψ - v.grad) := by
    rw [classicalGradient_add_of_contDiff hφ hψ]
    funext x; simp only [Pi.add_apply, Pi.sub_apply, W1pFunction.add_grad]; abel
  rw [e1, e2]
  calc _ ≤ w1pPairNorm Ω p (φ - u.toFun) (classicalGradient φ - u.grad) +
        w1pPairNorm Ω p (ψ - v.toFun) (classicalGradient ψ - v.grad) :=
        w1pPairNorm_add_le hp _ _ (hmeas φ u hφ) (hmeas ψ v hψ)
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hφlt hψlt
    _ = ε := ENNReal.add_halves ε

theorem ApproxW1p.sum {Ω : Set (Vec d)} {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {ι : Type*} (s : Finset ι)
    (v : ι → W1pFunction Ω (ENNReal.ofReal p)) (hv : ∀ j ∈ s, ApproxW1p Ω p (v j)) :
    ApproxW1p Ω p (∑ j ∈ s, v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ApproxW1p.zero Ω p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hv a (Finset.mem_insert_self a s)).add hp
      (ih fun j hj => hv j (Finset.mem_insert_of_mem hj))

section Atlas

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- A function in `W^{1,p}(Ω)` vanishing (with its gradient) on `Ω` off the support of the `j`-th
partition function is approximable. -/
theorem approxW1p_of_vanishing_chart (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (A : TraceAtlas Ω) {p : ℝ} (hp : 1 ≤ p) (j : Fin A.N)
    (w : W1pFunction Ω (ENNReal.ofReal p))
    (hw0 : ∀ x ∈ Ω, x ∉ tsupport (A.ζ j) → w.toFun x = 0)
    (hg0 : ∀ x ∈ Ω, x ∉ tsupport (A.ζ j) → w.grad x = 0) : ApproxW1p Ω p w := by
  intro ε hε
  obtain ⟨τ₀, hτ₀, hcov⟩ := chart_translate_cover (A.chart j) (A.ζ_compact j)
    (A.ζ_tsupport j)
  exact exists_smooth_approx_of_vanishing hΩo hΩb hp w (isClosed_tsupport _) hw0 hg0
    (A.chart j).dir hτ₀ hcov hε

/-- A function in `W^{1,p}(Ω)` vanishing (with its gradient) on `Ω ∩ V` is approximable. -/
theorem approxW1p_of_vanishing_interior (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (A : TraceAtlas Ω) {p : ℝ} (hp : 1 ≤ p) (w : W1pFunction Ω (ENNReal.ofReal p))
    (hw0 : ∀ x ∈ Ω, x ∈ A.V → w.toFun x = 0) (hg0 : ∀ x ∈ Ω, x ∈ A.V → w.grad x = 0) :
    ApproxW1p Ω p w := by
  intro ε hε
  refine exists_smooth_approx_of_vanishing hΩo hΩb hp w A.V_open.isClosed_compl
    (fun x hx hxK => hw0 x hx (by simpa using hxK))
    (fun x hx hxK => hg0 x hx (by simpa using hxK)) 0 one_pos ?_ hε
  intro τ _ _ x hx
  simp only [smul_zero, add_zero, compl_compl]
  by_cases hxΩ : x ∈ Ω
  · exact Or.inl hxΩ
  · refine Or.inr (A.frontier_subset ?_)
    rw [frontier, hΩo.interior_eq]
    exact ⟨hx, hxΩ⟩

end Atlas

end PDE.TraceLane
