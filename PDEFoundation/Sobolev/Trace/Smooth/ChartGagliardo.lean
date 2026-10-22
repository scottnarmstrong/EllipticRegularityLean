module

public import PDEFoundation.Sobolev.Trace.Smooth.ChartGag

/-!
# Per-chart Gagliardo bound

The chart-local part of the Gagliardo integral of `ζ u` is controlled by the flat Gagliardo integral
of the trace of the pullback (distances are non-decreasing under the chart map), which is bounded by
the half-space estimate; the far-pair error is controlled by `∫ |ζ u|^p dσ`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Comparison of the chart-local Gagliardo integral with the flat one. -/
theorem gag_local_le (φ : GraphChart Ω) {q p : ℝ} (hq : 0 < q) (hp : 0 < p)
    (f : Vec (n + 1) → ℝ) :
    ∫⁻ x, ∫⁻ y, gagKernel q p f x y ∂(boundarySurfaceMeasure Ω).restrict φ.dom
        ∂(boundarySurfaceMeasure Ω).restrict φ.dom ≤
      surfConst φ * (surfConst φ * flatGagliardo n q p (fun x' => f (φ.map (x', 0)))) := by
  refine (lintegral_sigma_iter_le φ (gagKernel q p f)).trans ?_
  gcongr
  unfold flatGagliardo
  refine lintegral_mono fun x' => lintegral_mono fun y' => ?_
  unfold gagKernel
  refine ENNReal.ofReal_le_ofReal ?_
  refine div_rpow_le_div_rpow (Real.rpow_nonneg (abs_nonneg _) _) (vecEuclideanNorm_nonneg _)
    (vecEuclideanNorm_sub_le_graphMap (i := φ.i) (γ := φ.γ) (sgn := φ.sgn) (x', (0 : ℝ))
      (y', (0 : ℝ))) hq fun h0 => ?_
  have : x' = y' := by
    have := vecEuclideanNorm_eq_zero_iff.1 h0
    exact sub_eq_zero.1 this
  subst this
  simp [Real.zero_rpow hp.ne']

/-- The Gagliardo integral of `ζ u` is bounded by `C N^p`. -/
theorem gagInt_chart_le (hΩo : IsOpen Ω) [IsFiniteMeasure (boundarySurfaceMeasure Ω)]
    (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ φ.dom) {p : ℝ} (hp : 1 < p) (hLp : ModelTraceLp n p)
    (hGag : ModelTraceGagliardo n p) :
    ∃ C : ℝ≥0, ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) → Measurable u →
      gagInt (boundarySurfaceMeasure Ω) ((n : ℝ) + p - 1) p (fun x => ζ x * u x) ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) ^ p := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < (n : ℝ) + p - 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨C₁, hC₁⟩ := sigma_lintegral_le hΩo φ hζ hζc hts hp.le hLp
  obtain ⟨Kc, hKc, hbd⟩ := upper_integral_bounds hΩo φ hζ hζc hts hp.le
  obtain ⟨CM, hCM⟩ := hGag
  obtain ⟨C₂, hC₂⟩ := gagInt_le_split (boundarySurfaceMeasure Ω) (q := (n : ℝ) + p - 1)
    hp.le hq.le (K := tsupport ζ) hζc φ.isOpen_dom hts
  set s := surfConst φ with hs
  set σu : ℝ≥0∞ := boundarySurfaceMeasure Ω univ with hσu
  set c : ℝ≥0∞ := s * (s * (CM * ENNReal.ofReal Kc ^ p)) + C₂ * σu * C₁ with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top (surfConst_ne_top φ) (ENNReal.mul_ne_top (surfConst_ne_top φ)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)))
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
        ENNReal.coe_ne_top
  refine ⟨c.toNNReal, fun u hu hum => ?_⟩
  rw [ENNReal.coe_toNNReal hcfin]
  have hm : Measurable fun x => ζ x * u x := hζ.continuous.measurable.mul hum
  have hfK : ∀ x ∉ tsupport ζ, ζ x * u x = 0 := fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]
  refine (hC₂ _ hm hfK).trans ?_
  have hA := hCM (pullback φ ζ u) (contDiffOn_pullback φ hζ hts hu)
    (exists_compact_pullback φ hζc u)
  have hB := (hbd u hu).2.2
  have hD := gag_local_le φ hq hp0 (fun x => ζ x * u x)
  calc _ ≤ s * (s * (CM * (ENNReal.ofReal Kc ^ p *
            w1pPairNorm Ω p u (classicalGradient u) ^ p))) +
          C₂ * σu * (C₁ * w1pPairNorm Ω p u (classicalGradient u) ^ p) := by
        gcongr
        · refine hD.trans ?_
          gcongr
          exact hA.trans (by gcongr)
        · exact hC₁ u hu
    _ = _ := by rw [hc]; ring

end PDE.TraceLane
