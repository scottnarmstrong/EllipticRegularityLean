module

public import PDEFoundation.Sobolev.Trace.Smooth.PullbackBound
public import PDEFoundation.Sobolev.Trace.Chart.Facts
public import PDEFoundation.Sobolev.Trace.Smooth.Scalar

/-!
# Transfer of `L^p` integrals from the half-space to `Ω`

The chart map is measure preserving, so a function on the open half-space which is bounded by
`Kc` times a function `g ∘ Ψ` on the points mapped into `Ω`, and vanishes elsewhere, has `p`-th
power integral at most `Kc^p` times the `p`-th power integral of `g` over `Ω`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem measurableSet_upperHalf (n : ℕ) : MeasurableSet (upperHalf n) :=
  MeasurableSet.univ.prod measurableSet_Ioi

theorem GraphChart.measurePreserving_map (φ : GraphChart Ω) :
    MeasurePreserving φ.map volume volume :=
  measurePreserving_graphMap φ.sgn_sq φ.γ_contDiff.continuous.measurable

theorem lintegral_upper_le (hΩo : IsOpen Ω) (φ : GraphChart Ω) {p Kc : ℝ} (hp : 0 < p)
    (hKc : 0 ≤ Kc) (g : Vec (n + 1) → ℝ) (hg0 : ∀ y, 0 ≤ g y) (H : Vec n × ℝ → ℝ)
    (hH : ∀ z ∈ upperHalf n, (φ.map z ∈ Ω → 0 ≤ H z ∧ H z ≤ Kc * g (φ.map z)) ∧
      (φ.map z ∉ Ω → H z = 0)) :
    ∫⁻ z in upperHalf n, ENNReal.ofReal (H z ^ p) ≤
      ENNReal.ofReal Kc ^ p * ∫⁻ x in Ω, ENNReal.ofReal (g x ^ p) := by
  set F : Vec (n + 1) → ℝ≥0∞ :=
    Ω.indicator (fun y => ENNReal.ofReal Kc ^ p * ENNReal.ofReal (g y ^ p)) with hF
  have h1 : ∫⁻ z in upperHalf n, ENNReal.ofReal (H z ^ p) ≤ ∫⁻ z in upperHalf n, F (φ.map z) := by
    refine setLIntegral_mono' (measurableSet_upperHalf n) fun z hz => ?_
    by_cases hzΩ : φ.map z ∈ Ω
    · obtain ⟨h0, h1⟩ := (hH z hz).1 hzΩ
      rw [hF, indicator_of_mem hzΩ, ENNReal.ofReal_rpow_of_nonneg hKc hp.le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hKc (hg0 _)]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 h1 hp.le)
    · rw [(hH z hz).2 hzΩ, Real.zero_rpow hp.ne']
      simp
  have h2 : ∫⁻ z in upperHalf n, F (φ.map z) ≤ ∫⁻ z, F (φ.map z) :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have h3 : ∫⁻ z, F (φ.map z) = ∫⁻ y, F y :=
    φ.measurePreserving_map.lintegral_comp_emb φ.homeo.measurableEmbedding F
  have h4 : ∫⁻ y, F y = ENNReal.ofReal Kc ^ p * ∫⁻ x in Ω, ENNReal.ofReal (g x ^ p) := by
    rw [hF, lintegral_indicator hΩo.measurableSet,
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
  exact h1.trans (h2.trans (h3.le.trans h4.le))

theorem gAbs_nonneg (u : Vec (n + 1) → ℝ) (y : Vec (n + 1)) : 0 ≤ gAbs u y := by
  unfold gAbs; have := vecEuclideanNorm_nonneg (classicalGradient u y); positivity

/-- The `p`-th power integral of `|u| + |∇u|` over `Ω` is at most `N^p`. -/
theorem lintegral_gAbs_le (hΩo : IsOpen Ω) {p : ℝ} (hp : 1 ≤ p) {u : Vec (n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u (closure Ω)) :
    ∫⁻ x in Ω, ENNReal.ofReal (gAbs u x ^ p) ≤
      w1pPairNorm Ω p u (classicalGradient u) ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hu1 := aestronglyMeasurable_of_contDiffOn_closure hΩo hu
  have hg1 : AEStronglyMeasurable (fun x => vecEuclideanNorm (classicalGradient u x))
      (volumeOn Ω) :=
    continuous_vecEuclideanNorm.comp_aestronglyMeasurable
      (aestronglyMeasurable_classicalGradient hΩo hu)
  have hgm : AEStronglyMeasurable (gAbs u) (volumeOn Ω) := by
    unfold gAbs
    exact hu1.norm.add hg1 |>.congr (Eventually.of_forall fun x => by simp)
  have h1 : ∫⁻ x in Ω, ENNReal.ofReal (gAbs u x ^ p) = eLpNorm (gAbs u) (ENNReal.ofReal p)
      (volumeOn Ω) ^ p := by
    rw [← lintegral_ofReal_rpow_eq hp0 hgm]
    refine lintegral_congr fun x => ?_
    rw [abs_of_nonneg (gAbs_nonneg u x)]
  rw [h1]
  refine ENNReal.rpow_le_rpow ?_ hp0.le
  have h2 : gAbs u = (fun x => ‖u x‖) + fun x => vecEuclideanNorm (classicalGradient u x) := by
    funext x; simp [gAbs]
  rw [h2]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_norm _ hu1]
  rfl

end PDE.TraceLane
