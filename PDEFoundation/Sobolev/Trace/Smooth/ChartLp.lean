module

public import PDEFoundation.Sobolev.Trace.Smooth.Transfer
public import PDEFoundation.Sobolev.Trace.Smooth.Sigma
public import PDEFoundation.Sobolev.Trace.Assembly.Props

/-!
# `L^p(σ)` bound for a localised function

For a chart `φ`, a cutoff `ζ` supported in the chart cylinder, and `u ∈ C¹(Ω̄)`, the pullback
`v = (ζ u) ∘ Ψ` has half-space `p`-integrals bounded by `Kc^p N^p` (with `N` the `W^{1,p}` pair
norm of `u`), the half-space trace bound turns this into a bound on `∫ |v(x', 0)|^p`, and the
surface comparison gives `∫ |ζ u|^p dσ ≤ C N^p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The half-space integrals of `|v|`, `|∂ₜ v|`, `|∇ v|` are bounded by `Kc^p N^p`. -/
theorem upper_integral_bounds (hΩo : IsOpen Ω) (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hts : tsupport ζ ⊆ φ.dom) {p : ℝ}
    (hp : 1 ≤ p) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) →
      (∫⁻ z in upperHalf n, ENNReal.ofReal (|pullback φ ζ u z| ^ p) ≤
        ENNReal.ofReal Kc ^ p * w1pPairNorm Ω p u (classicalGradient u) ^ p) ∧
      (∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv (pullback φ ζ u) z| ^ p) ≤
        ENNReal.ofReal Kc ^ p * w1pPairNorm Ω p u (classicalGradient u) ^ p) ∧
      (∫⁻ z in upperHalf n, ENNReal.ofReal (modelGradNorm (pullback φ ζ u) z ^ p) ≤
        ENNReal.ofReal Kc ^ p * w1pPairNorm Ω p u (classicalGradient u) ^ p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Kc, hKc, hbd⟩ := exists_pullback_bound hΩo φ hζ hζc
  refine ⟨Kc, hKc, fun u hu => ?_⟩
  have hI := lintegral_gAbs_le hΩo hp hu
  have hmono : ∀ H : Vec n × ℝ → ℝ,
      (∀ z ∈ upperHalf n, (φ.map z ∈ Ω → 0 ≤ H z ∧ H z ≤ Kc * gAbs u (φ.map z)) ∧
        (φ.map z ∉ Ω → H z = 0)) →
      ∫⁻ z in upperHalf n, ENNReal.ofReal (H z ^ p) ≤
        ENNReal.ofReal Kc ^ p * w1pPairNorm Ω p u (classicalGradient u) ^ p := fun H hH =>
    (lintegral_upper_le hΩo φ hp0 hKc (gAbs u) (gAbs_nonneg u) H hH).trans
      (by gcongr)
  refine ⟨hmono _ fun z hz => ⟨fun hzΩ => ⟨abs_nonneg _, (hbd u hu z hzΩ).1⟩, fun hzΩ => ?_⟩,
    hmono _ fun z hz => ⟨fun hzΩ => ⟨abs_nonneg _, (hbd u hu z hzΩ).2.1⟩, fun hzΩ => ?_⟩,
    hmono _ fun z hz => ⟨fun hzΩ => ⟨Real.sqrt_nonneg _, (hbd u hu z hzΩ).2.2⟩, fun hzΩ => ?_⟩⟩
  · rw [(pullback_deriv_eq_zero φ hts hz.2 hzΩ).1, abs_zero]
  · rw [(pullback_deriv_eq_zero φ hts hz.2 hzΩ).2.1, abs_zero]
  · exact (pullback_deriv_eq_zero φ hts hz.2 hzΩ).2.2

/-- The trace of the pullback in `L^p(ℝⁿ)`. -/
theorem pullback_trace_lintegral_le (hΩo : IsOpen Ω) (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hts : tsupport ζ ⊆ φ.dom) {p : ℝ}
    (hp : 1 ≤ p) (hLp : ModelTraceLp n p) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) →
      ∫⁻ x', ENNReal.ofReal (|pullback φ ζ u (x', 0)| ^ p) ≤
        ENNReal.ofReal p * (ENNReal.ofReal Kc ^ p *
          w1pPairNorm Ω p u (classicalGradient u) ^ p) := by
  obtain ⟨Kc, hKc, hbd⟩ := upper_integral_bounds hΩo φ hζ hζc hts hp
  refine ⟨Kc, hKc, fun u hu => ?_⟩
  obtain ⟨h1, h2, -⟩ := hbd u hu
  set J : ℝ≥0∞ := ENNReal.ofReal Kc ^ p * w1pPairNorm Ω p u (classicalGradient u) ^ p with hJ
  have hv := hLp (pullback φ ζ u) (contDiffOn_pullback φ hζ hts hu)
    (exists_compact_pullback φ hζc u)
  refine hv.trans ?_
  have hp0 : 0 < p := by linarith
  have ha : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
  have hb : 0 ≤ 1 / p := by positivity
  calc _ ≤ ENNReal.ofReal p * J ^ ((p - 1) / p) * J ^ (1 / p) := by gcongr
    _ = ENNReal.ofReal p * J := by
        rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ ha hb]
        have : (p - 1) / p + 1 / p = 1 := by field_simp; ring
        rw [this, ENNReal.rpow_one]

end PDE.TraceLane
