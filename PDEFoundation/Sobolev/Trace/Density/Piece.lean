module

public import PDEFoundation.Sobolev.Trace.Density.Approx
public import PDEFoundation.Sobolev.Trace.Density.Glue

/-!
# Approximation of a `W^{1,p}(Ω)` function vanishing off a closed set

If `w ∈ W^{1,p}(Ω)` vanishes (together with its gradient) on `Ω \ K` for a closed `K`, and
`closure Ω + τ e ⊆ Ω ∪ Kᶜ` for small `τ > 0`, then `w` is a `W^{1,p}(Ω)`-limit of smooth
functions (`exists_smooth_approx_of_vanishing`).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal

variable {d : ℕ}

theorem exists_smooth_approx_of_vanishing {Ω : Set (Vec d)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {p : ℝ} (hp : 1 ≤ p)
    (w : W1pFunction Ω (ENNReal.ofReal p)) {K : Set (Vec d)} (hK : IsClosed K)
    (hw0 : ∀ x ∈ Ω, x ∉ K → w.toFun x = 0) (hg0 : ∀ x ∈ Ω, x ∉ K → w.grad x = 0)
    (e : Vec d) {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hcov : ∀ τ : ℝ, 0 < τ → τ < τ₀ → ∀ x ∈ closure Ω, x + τ • e ∈ Ω ∪ Kᶜ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      w1pPairNorm Ω p (φ - w.toFun) (classicalGradient φ - w.grad) < ε := by
  have hmeasΩ := hΩo.measurableSet
  have hW : MemLp (Ω.indicator w.toFun) (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict hmeasΩ).2 w.memLp
  have hG : ∀ i, MemLp (fun x => Ω.indicator w.grad x i) (ENNReal.ofReal p) volume := by
    intro i
    have : (fun x => Ω.indicator w.grad x i) = Ω.indicator (fun x => w.grad x i) := by
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    rw [this]
    exact (memLp_indicator_iff_restrict hmeasΩ).2 (w.gradMemLp i)
  have hweak := hasWeakGradientOn_indicator_union_compl hΩo hK w.hasWeakGradient hw0 hg0
  obtain ⟨φ, hφ, hlt⟩ := exists_smooth_approx_of_weak hmeasΩ hΩb hp (hΩo.union hK.isOpen_compl)
    hW hG hweak e hτ₀ hcov hε
  refine ⟨φ, hφ, ?_⟩
  have hae1 : (Ω.indicator w.toFun) =ᵐ[volumeOn Ω] w.toFun :=
    (ae_restrict_iff' hmeasΩ).2 (Eventually.of_forall fun x hx => indicator_of_mem hx _)
  have hae2 : (Ω.indicator w.grad) =ᵐ[volumeOn Ω] w.grad :=
    (ae_restrict_iff' hmeasΩ).2 (Eventually.of_forall fun x hx => indicator_of_mem hx _)
  rw [← w1pPairNorm_congr_ae (Ω := Ω) (p := p) (f := φ - Ω.indicator w.toFun)
    (g := φ - w.toFun) (F := classicalGradient φ - Ω.indicator w.grad)
    (G := classicalGradient φ - w.grad) (hae1.mono fun x hx => by simp [hx])
    (hae2.mono fun x hx => by simp [hx])]
  exact hlt

end PDE.TraceLane
