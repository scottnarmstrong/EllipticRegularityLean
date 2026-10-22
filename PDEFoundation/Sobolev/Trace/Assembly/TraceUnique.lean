module

public import PDEFoundation.Sobolev.Trace.Assembly.Fatou
public import PDEFoundation.Sobolev.Trace.Assembly.Props

/-!
# Uniqueness and bounds of traces (manuscript Step 5)

From the `L^p` part of the smooth trace bound, traces are unique `σ`-a.e.; from the full smooth
trace bound, every trace satisfies the Besov bound (Fatou for the seminorm along an a.e.
convergent subsequence).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Set (Vec d)} {p : ℝ}

/-- The pair norm of `ψ - u` controls that of `ψ - ψ'` against `ψ' - u`. -/
theorem w1pPairNorm_sub_sub_le (hΩo : IsOpen Ω) (hp : 1 ≤ p)
    (u : W1pFunction Ω (ENNReal.ofReal p)) {ψ ψ' : Vec d → ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (closure Ω)) (hψ' : ContDiffOn ℝ 1 ψ' (closure Ω)) :
    w1pPairNorm Ω p (ψ - ψ') (classicalGradient (ψ - ψ')) ≤
      w1pPairNorm Ω p (ψ - u.toFun) (classicalGradient ψ - u.grad) +
        w1pPairNorm Ω p (ψ' - u.toFun) (classicalGradient ψ' - u.grad) := by
  have hcongr : w1pPairNorm Ω p (ψ - ψ') (classicalGradient (ψ - ψ')) =
      w1pPairNorm Ω p ((ψ - u.toFun) - (ψ' - u.toFun))
        ((classicalGradient ψ - u.grad) - (classicalGradient ψ' - u.grad)) := by
    refine w1pPairNorm_congr_ae (Eventually.of_forall fun x => by simp) ?_
    filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
    rw [classicalGradient_sub_of_mem hΩo hψ hψ' hx]
    simp
  rw [hcongr]
  exact w1pPairNorm_sub_le hp _ _
    ((aestronglyMeasurable_classicalGradient hΩo hψ).sub (aestronglyMeasurable_w1p_grad u))
    ((aestronglyMeasurable_classicalGradient hΩo hψ').sub (aestronglyMeasurable_w1p_grad u))

/-- The pair norm of `ψ` is controlled by that of `ψ - u` and the norm of `u`. -/
theorem w1pPairNorm_le_sub_add (hΩo : IsOpen Ω) (hp : 1 ≤ p)
    (u : W1pFunction Ω (ENNReal.ofReal p)) {ψ : Vec d → ℝ} (hψ : ContDiffOn ℝ 1 ψ (closure Ω)) :
    w1pPairNorm Ω p ψ (classicalGradient ψ) ≤
      w1pPairNorm Ω p (ψ - u.toFun) (classicalGradient ψ - u.grad) + w1pNorm Ω p u := by
  have h := w1pPairNorm_add_le (Ω := Ω) hp (ψ - u.toFun) u.toFun
    ((aestronglyMeasurable_classicalGradient hΩo hψ).sub (aestronglyMeasurable_w1p_grad u))
    (aestronglyMeasurable_w1p_grad u)
  simpa [w1pNorm] using h

/-- **Uniqueness of traces.** -/
theorem isTraceOf_ae_unique (hΩo : IsOpen Ω) (hp : 1 < p) {C : ℝ≥0}
    (hS : ∀ φ : Vec d → ℝ, ContDiffOn ℝ 1 φ (closure Ω) →
      eLpNorm φ (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        (C : ℝ≥0∞) * w1pPairNorm Ω p φ (classicalGradient φ))
    (u : W1pFunction Ω (ENNReal.ofReal p)) {g g' : Vec d → ℝ}
    (hg : IsTraceOf Ω p u g) (hg' : IsTraceOf Ω p u g') :
    g =ᵐ[boundarySurfaceMeasure Ω] g' := by
  obtain ⟨hgm, ψ, hψ, hψu, hψg⟩ := hg
  obtain ⟨hgm', ψ', hψ', hψu', hψg'⟩ := hg'
  have hq1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hbound : ∀ k, eLpNorm (g - g') (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
      eLpNorm (ψ k - g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + (C : ℝ≥0∞) *
        (w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) +
          w1pPairNorm Ω p (ψ' k - u.toFun) (classicalGradient (ψ' k) - u.grad)) +
        eLpNorm (ψ' k - g') (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
    intro k
    have e : g - g' = -(ψ k - g) + (ψ k - ψ' k) + (ψ' k - g') := by abel
    rw [e]
    have hmid : eLpNorm (ψ k - ψ' k) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤ (C : ℝ≥0∞) *
        (w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) +
          w1pPairNorm Ω p (ψ' k - u.toFun) (classicalGradient (ψ' k) - u.grad)) := by
      refine (hS _ ((hψ k).sub (hψ' k))).trans ?_
      gcongr
      exact w1pPairNorm_sub_sub_le hΩo hp.le u (hψ k) (hψ' k)
    calc eLpNorm (-(ψ k - g) + (ψ k - ψ' k) + (ψ' k - g')) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω)
        ≤ eLpNorm (-(ψ k - g) + (ψ k - ψ' k)) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + eLpNorm (ψ' k - g') (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) :=
          eLpNorm_add_le hq1
      _ ≤ (eLpNorm (-(ψ k - g)) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + eLpNorm (ψ k - ψ' k) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω)) + eLpNorm (ψ' k - g') (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) :=
          add_le_add (eLpNorm_add_le hq1) le_rfl
      _ ≤ _ := by
          rw [eLpNorm_neg]
          exact add_le_add (add_le_add le_rfl hmid) le_rfl
  have hlim : Tendsto (fun k => eLpNorm (ψ k - g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) + (C : ℝ≥0∞) *
      (w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) +
        w1pPairNorm Ω p (ψ' k - u.toFun) (classicalGradient (ψ' k) - u.grad)) +
      eLpNorm (ψ' k - g') (ENNReal.ofReal p) (boundarySurfaceMeasure Ω)) atTop (𝓝 0) := by
    have h := (hψg.add (ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) (hψu.add hψu')
      (Or.inr ENNReal.coe_ne_top))).add hψg'
    simpa using h
  have h0 : eLpNorm (g - g') (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  have hq0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have := (eLpNorm_eq_zero_iff hq0).1 h0
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end PDE.TraceLane
