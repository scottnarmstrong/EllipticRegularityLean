module

public import PDEFoundation.Sobolev.Trace.Smooth.ChartLp
public import PDEFoundation.Sobolev.Trace.Smooth.Split

/-!
# Per-chart bounds: surface `L^p` norm and Gagliardo seminorm

For a chart `φ` and a cutoff `ζ` supported in its cylinder, `f = ζ u` satisfies
`∫ |f|^p dσ ≤ C N^p` and `∬_{dom×dom} |f x - f y|^p / |x-y|^q ≤ C N^p`, hence (adding the far-pair
error from `gagInt_le_split`) `gagInt σ q p f ≤ C N^p`, with `N` the `W^{1,p}` pair norm of `u`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem div_rpow_le_div_rpow {a r s q : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hsr : s ≤ r) (hq : 0 < q)
    (h0 : s = 0 → a = 0) : a / r ^ q ≤ a / s ^ q := by
  rcases hs.eq_or_lt with hs0 | hs0
  · rw [h0 hs0.symm]; simp
  · exact div_le_div_of_nonneg_left ha (Real.rpow_pos_of_pos hs0 _)
      (Real.rpow_le_rpow hs0.le hsr hq.le)

/-- The `σ`-integral of `|ζ u|^p` is at most `C N^p`. -/
theorem sigma_lintegral_le (hΩo : IsOpen Ω) (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hts : tsupport ζ ⊆ φ.dom) {p : ℝ}
    (hp : 1 ≤ p) (hLp : ModelTraceLp n p) :
    ∃ C : ℝ≥0, ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) →
      ∫⁻ x, ENNReal.ofReal (|ζ x * u x| ^ p) ∂boundarySurfaceMeasure Ω ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) ^ p := by
  obtain ⟨Kc, hKc, hbd⟩ := pullback_trace_lintegral_le hΩo φ hζ hζc hts hp hLp
  have hp0 : 0 < p := by linarith
  set c : ℝ≥0∞ := surfConst φ * (ENNReal.ofReal p * ENNReal.ofReal Kc ^ p) with hc
  have hcfin : c ≠ ⊤ := ENNReal.mul_ne_top (surfConst_ne_top φ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top))
  refine ⟨c.toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal hcfin]
  have hsupp : ∀ x ∉ φ.dom, ENNReal.ofReal (|ζ x * u x| ^ p) = 0 := fun x hx => by
    have : ζ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))
    simp [this, Real.zero_rpow hp0.ne']
  refine (lintegral_sigma_le φ _ hsupp).trans ?_
  calc surfConst φ * ∫⁻ x', ENNReal.ofReal (|ζ (φ.map (x', 0)) * u (φ.map (x', 0))| ^ p)
      ≤ surfConst φ * (ENNReal.ofReal p * (ENNReal.ofReal Kc ^ p *
          w1pPairNorm Ω p u (classicalGradient u) ^ p)) := by
        gcongr
        exact hbd u hu
    _ = _ := by rw [hc]; ring

/-- The surface `L^p` norm of `ζ u`. -/
theorem sigma_eLpNorm_le (hΩo : IsOpen Ω) (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) (hts : tsupport ζ ⊆ φ.dom) {p : ℝ}
    (hp : 1 ≤ p) (hLp : ModelTraceLp n p) :
    ∃ C : ℝ≥0, ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) → Measurable u →
      eLpNorm (fun x => ζ x * u x) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) := by
  obtain ⟨C, hC⟩ := sigma_lintegral_le hΩo φ hζ hζc hts hp hLp
  have hp0 : 0 < p := by linarith
  refine ⟨C ^ (1 / p), fun u hu hum => ?_⟩
  have hm : Measurable fun x => ζ x * u x := hζ.continuous.measurable.mul hum
  rw [eLpNorm_eq_lintegral_ofReal_rpow hp0 hm.aestronglyMeasurable]
  refine (ENNReal.rpow_le_rpow (hC u hu) (by positivity)).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne',
    ENNReal.rpow_one]
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 1 / p)]

end PDE.TraceLane
