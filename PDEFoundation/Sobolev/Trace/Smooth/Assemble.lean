module

public import PDEFoundation.Sobolev.Trace.Smooth.ChartGagliardo
public import PDEFoundation.Sobolev.Trace.Smooth.GagSum

/-!
# The smooth trace bound from the half-space estimates

Manuscript Step 4: patching the per-chart bounds with the partition of unity.  A measurable
representative of `u ∈ C¹(Ω̄)` is used throughout (the surface measure and the Lebesgue measure on
`Ω` do not see the difference), so that all integrands are measurable.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

theorem exponent_eq (p : ℝ) (hp : p ≠ 0) :
    (((n + 1 : ℕ) : ℝ) - 1 + (1 - 1 / p) * p) = (n : ℝ) + p - 1 := by
  push_cast
  field_simp
  ring

/-- On the frontier, `u` is the sum of its localisations. -/
theorem ae_eq_sum_localisations (A : TraceAtlas Ω) (u : Vec (n + 1) → ℝ) :
    u =ᵐ[boundarySurfaceMeasure Ω] fun x => ∑ j, A.ζ j x * u x := by
  have h := measure_eq_zero_iff_ae_notMem.1 (boundarySurfaceMeasure_compl_frontier (Ω := Ω))
  filter_upwards [h] with x hx
  have hx' : x ∈ frontier Ω := by simpa using hx
  rw [← Finset.sum_mul, A.sum_eq_one x (A.frontier_subset hx'), one_mul]

/-- The bound for measurable `u`. -/
theorem smoothTraceBound_of_measurable {Ω : Set (Vec (n + 1))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (A : TraceAtlas Ω) {p : ℝ} (hp : 1 < p)
    (hLp : ModelTraceLp n p) (hGag : ModelTraceGagliardo n p) :
    ∃ C : ℝ≥0, ∀ u : Vec (n + 1) → ℝ, ContDiffOn ℝ 1 u (closure Ω) → Measurable u →
      eLpNorm u (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) ∧
      gagliardoSeminorm Ω (1 - 1 / p) p u ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) := by
  have := boundarySurfaceMeasure_isFiniteMeasure A hΩb
  have hp0 : 0 < p := by linarith
  have hζ : ∀ j, ContDiff ℝ 1 (A.ζ j) := fun j =>
    (A.ζ_smooth j).of_le (by exact_mod_cast le_top)
  choose C₁ hC₁ using fun j => sigma_eLpNorm_le hΩo (A.chart j) (hζ j) (A.ζ_compact j)
    (A.ζ_tsupport j) hp.le hLp
  choose C₂ hC₂ using fun j => gagInt_chart_le hΩo (A.chart j) (hζ j) (A.ζ_compact j)
    (A.ζ_tsupport j) hp hLp hGag
  refine ⟨∑ j, C₁ j + ∑ j, (C₂ j) ^ (1 / p), fun u hu hum => ?_⟩
  have hae := ae_eq_sum_localisations A u
  have hfm : ∀ j, Measurable fun x => A.ζ j x * u x := fun j =>
    (hζ j).continuous.measurable.mul hum
  constructor
  · calc _ = eLpNorm (∑ j, fun x => A.ζ j x * u x) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
          rw [eLpNorm_congr_ae hae]; congr 1; funext x; simp
      _ ≤ ∑ j, eLpNorm (fun x => A.ζ j x * u x) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) :=
          eLpNorm_sum_le (by simpa using hp.le)
      _ ≤ ∑ j, (C₁ j : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) :=
          Finset.sum_le_sum fun j _ => hC₁ j u hu hum
      _ = (∑ j, (C₁ j : ℝ≥0∞)) * w1pPairNorm Ω p u (classicalGradient u) := by
          rw [Finset.sum_mul]
      _ ≤ _ := by
          push_cast
          gcongr
          exact le_self_add
  · rw [gagliardoSeminorm_eq, exponent_eq p hp0.ne', gagInt_congr_ae hae]
    refine (gagInt_rpow_sum_le _ hp.le Finset.univ (fun j x => A.ζ j x * u x) hfm).trans ?_
    calc ∑ j, gagInt (boundarySurfaceMeasure Ω) ((n : ℝ) + p - 1) p (fun x => A.ζ j x * u x) ^
          (1 / p)
        ≤ ∑ j, ((C₂ j : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) ^ p) ^ (1 / p) :=
          Finset.sum_le_sum fun j _ =>
            ENNReal.rpow_le_rpow (hC₂ j u hu hum) (by positivity)
      _ = ∑ j, ((C₂ j ^ (1 / p) : ℝ≥0) : ℝ≥0∞) * w1pPairNorm Ω p u (classicalGradient u) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
            ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 1 / p)]
      _ = (∑ j, ((C₂ j ^ (1 / p) : ℝ≥0) : ℝ≥0∞)) *
            w1pPairNorm Ω p u (classicalGradient u) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          push_cast
          gcongr
          exact le_add_self

/-- Manuscript Step 4: the trace bound for `C¹(Ω̄)` functions follows from the half-space bounds. -/
theorem smoothTraceBound_of_model {n : ℕ} {Ω : Set (Vec (n + 1))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (A : TraceAtlas Ω) {p : ℝ} (hp : 1 < p)
    (hLp : ModelTraceLp n p) (hGag : ModelTraceGagliardo n p) : SmoothTraceBound Ω p := by
  classical
  obtain ⟨C, hC⟩ := smoothTraceBound_of_measurable hΩo hΩb A hp hLp hGag
  refine ⟨C, fun u hu => ?_⟩
  set ũ : Vec (n + 1) → ℝ := (closure Ω).piecewise u 0 with hũ
  have hmeas : Measurable ũ :=
    ContinuousOn.measurable_piecewise (hu.continuousOn) continuous_zero.continuousOn
      isClosed_closure.measurableSet
  have hcl : ∀ x ∈ closure Ω, ũ x = u x := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hu' : ContDiffOn ℝ 1 ũ (closure Ω) := hu.congr hcl
  have hσ : u =ᵐ[boundarySurfaceMeasure Ω] ũ := by
    have h := measure_eq_zero_iff_ae_notMem.1 (boundarySurfaceMeasure_compl_frontier (Ω := Ω))
    filter_upwards [h] with x hx
    have hx' : x ∈ frontier Ω := by simpa using hx
    exact (hcl x (frontier_subset_closure hx')).symm
  have hvol : u =ᵐ[volumeOn Ω] ũ :=
    (ae_restrict_iff' hΩo.measurableSet).2 (Eventually.of_forall fun x hx =>
      (hcl x (subset_closure hx)).symm)
  have hgrad : classicalGradient u =ᵐ[volumeOn Ω] classicalGradient ũ := by
    refine (ae_restrict_iff' hΩo.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
    have hev : ũ =ᶠ[𝓝 x] u :=
      Filter.mem_of_superset (hΩo.mem_nhds hx) fun y hy => hcl y (subset_closure hy)
    funext i
    simp [classicalGradient, hev.fderiv_eq]
  have hN : w1pPairNorm Ω p u (classicalGradient u) =
      w1pPairNorm Ω p ũ (classicalGradient ũ) := w1pPairNorm_congr_ae hvol hgrad
  obtain ⟨h1, h2⟩ := hC ũ hu' hmeas
  rw [hN, eLpNorm_congr_ae hσ, gagliardoSeminorm_eq, gagInt_congr_ae hσ,
    ← gagliardoSeminorm_eq]
  exact ⟨h1, h2⟩

end PDE.TraceLane
