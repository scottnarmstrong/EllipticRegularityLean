module

public import PDEFoundation.Sobolev.Trace.Assembly.TraceUnique

/-!
# The characterization of the trace space from the trace inequality and the right inverse

`characterization_of`: for fixed `Ω`, `p`, the conclusions of `trace_inequality` and
`trace_right_inverse` give the conclusion of `trace_space_characterization`.  The trace operator
`T` is a choice of a trace for each `u`; it is a.e.-linear because traces of sums are sums of
traces and traces are unique.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Set (Vec d)} {p : ℝ}

/-- Traces of sums are sums of traces. -/
theorem IsTraceOf.add (hΩo : IsOpen Ω) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    {u v : W1pFunction Ω (ENNReal.ofReal p)} {g h : Vec d → ℝ}
    (hg : IsTraceOf Ω p u g) (hh : IsTraceOf Ω p v h) : IsTraceOf Ω p (u + v) (g + h) := by
  obtain ⟨hgm, ψ, hψ, hψu, hψg⟩ := hg
  obtain ⟨hhm, χ, hχ, hχv, hχh⟩ := hh
  have hq1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  refine ⟨hgm.add hhm, fun k => ψ k + χ k, fun k => (hψ k).add (hχ k), ?_, ?_⟩
  · have hle : ∀ k, w1pPairNorm Ω p (ψ k + χ k - (u + v).toFun)
        (classicalGradient (ψ k + χ k) - (u + v).grad) ≤
        w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) +
          w1pPairNorm Ω p (χ k - v.toFun) (classicalGradient (χ k) - v.grad) := by
      intro k
      have hcongr : w1pPairNorm Ω p (ψ k + χ k - (u + v).toFun)
          (classicalGradient (ψ k + χ k) - (u + v).grad) =
          w1pPairNorm Ω p ((ψ k - u.toFun) + (χ k - v.toFun))
            ((classicalGradient (ψ k) - u.grad) + (classicalGradient (χ k) - v.grad)) := by
        refine w1pPairNorm_congr_ae (Eventually.of_forall fun x => ?_) ?_
        · simp only [Pi.add_apply, Pi.sub_apply, W1pFunction.add_toFun]; ring
        · filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
          have hn : closure Ω ∈ 𝓝 x := mem_of_superset (hΩo.mem_nhds hx) subset_closure
          have h1 : DifferentiableAt ℝ (ψ k) x :=
            (((hψ k).differentiableOn one_ne_zero) x (subset_closure hx)).differentiableAt hn
          have h2 : DifferentiableAt ℝ (χ k) x :=
            (((hχ k).differentiableOn one_ne_zero) x (subset_closure hx)).differentiableAt hn
          funext i
          simp only [classicalGradient, Pi.add_apply, Pi.sub_apply, W1pFunction.add_grad,
            fderiv_add h1 h2, add_apply]
          ring
      rw [hcongr]
      exact w1pPairNorm_add_le hp.le _ _
        ((aestronglyMeasurable_classicalGradient hΩo (hψ k)).sub (aestronglyMeasurable_w1p_grad u))
        ((aestronglyMeasurable_classicalGradient hΩo (hχ k)).sub (aestronglyMeasurable_w1p_grad v))
    have h := hψu.add hχv
    rw [add_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) hle
  · have hle : ∀ k, eLpNorm (ψ k + χ k - (g + h)) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) ≤
        eLpNorm (ψ k - g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) +
          eLpNorm (χ k - h) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
      intro k
      have e : ψ k + χ k - (g + h) = (ψ k - g) + (χ k - h) := by abel
      rw [e]
      exact eLpNorm_add_le hq1
    have hs := hψg.add hχh
    rw [add_zero] at hs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le) hle

/-- Traces of scalar multiples are scalar multiples of traces. -/
theorem IsTraceOf.smul (hΩo : IsOpen Ω) {u : W1pFunction Ω (ENNReal.ofReal p)} {g : Vec d → ℝ}
    (hg : IsTraceOf Ω p u g) (a : ℝ) : IsTraceOf Ω p (a • u) (a • g) := by
  obtain ⟨hgm, ψ, hψ, hψu, hψg⟩ := hg
  refine ⟨hgm.const_smul a, fun k => a • ψ k, fun k => (hψ k).const_smul a, ?_, ?_⟩
  · have heq : ∀ k, w1pPairNorm Ω p (a • ψ k - (a • u).toFun)
        (classicalGradient (a • ψ k) - (a • u).grad) = ENNReal.ofReal |a| *
          w1pPairNorm Ω p (ψ k - u.toFun) (classicalGradient (ψ k) - u.grad) := by
      intro k
      have hcongr : w1pPairNorm Ω p (a • ψ k - (a • u).toFun)
          (classicalGradient (a • ψ k) - (a • u).grad) =
          w1pPairNorm Ω p (a • (ψ k - u.toFun)) (a • (classicalGradient (ψ k) - u.grad)) := by
        refine w1pPairNorm_congr_ae (Eventually.of_forall fun x => ?_) ?_
        · simp only [Pi.smul_apply, Pi.sub_apply, W1pFunction.smul_toFun, smul_eq_mul]; ring
        · filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
          have hn : closure Ω ∈ 𝓝 x := mem_of_superset (hΩo.mem_nhds hx) subset_closure
          have h1 : DifferentiableAt ℝ (ψ k) x :=
            (((hψ k).differentiableOn one_ne_zero) x (subset_closure hx)).differentiableAt hn
          funext i
          simp only [classicalGradient, Pi.smul_apply, Pi.sub_apply, W1pFunction.smul_grad,
            fderiv_const_smul h1, smul_apply, smul_eq_mul]
          ring
      rw [hcongr]
      unfold w1pPairNorm
      have hn : (fun x => vecEuclideanNorm ((a • (classicalGradient (ψ k) - u.grad)) x)) =
          |a| • fun x => vecEuclideanNorm ((classicalGradient (ψ k) - u.grad) x) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        exact vecEuclideanNorm_smul _ _
      rw [hn, eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        Real.enorm_eq_ofReal_abs, abs_abs, mul_add]
    simp_rw [heq]
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |a|) hψu
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h
  · have heq : ∀ k, eLpNorm (a • ψ k - a • g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) =
        ENNReal.ofReal |a| * eLpNorm (ψ k - g) (ENNReal.ofReal p) (boundarySurfaceMeasure Ω) := by
      intro k
      rw [← smul_sub, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    simp_rw [heq]
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |a|) hψg
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h

/-- **Characterization of the trace space** from the conclusions of the trace inequality and of
the right inverse (for fixed `Ω`, `p`). -/
theorem characterization_of (hΩo : IsOpen Ω) (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (hTI : ∃ C : ℝ≥0, ∀ u : W1pFunction Ω (ENNReal.ofReal p),
      (∃ g, IsTraceOf Ω p u g) ∧
      (∀ g g', IsTraceOf Ω p u g → IsTraceOf Ω p u g' →
        g =ᵐ[boundarySurfaceMeasure Ω] g') ∧
      ∀ g, IsTraceOf Ω p u g →
        besovNorm Ω (1 - 1 / p) p g ≤ (C : ℝ≥0∞) * w1pNorm Ω p u)
    (hRI : ∃ (C : ℝ≥0) (E : (Vec d → ℝ) → W1pFunction Ω (ENNReal.ofReal p)),
      (∀ g h, IsBesov Ω (1 - 1 / p) p g → IsBesov Ω (1 - 1 / p) p h → E (g + h) = E g + E h) ∧
      (∀ (a : ℝ) g, IsBesov Ω (1 - 1 / p) p g → E (a • g) = a • E g) ∧
      ∀ g, IsBesov Ω (1 - 1 / p) p g →
        IsTraceOf Ω p (E g) g ∧
        w1pNorm Ω p (E g) ≤ (C : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g) :
    ∃ (C : ℝ≥0) (T : W1pFunction Ω (ENNReal.ofReal p) → Vec d → ℝ)
      (E : (Vec d → ℝ) → W1pFunction Ω (ENNReal.ofReal p)),
      (∀ u, IsTraceOf Ω p u (T u) ∧ IsBesov Ω (1 - 1 / p) p (T u) ∧
        besovNorm Ω (1 - 1 / p) p (T u) ≤ (C : ℝ≥0∞) * w1pNorm Ω p u) ∧
      (∀ u v, T (u + v) =ᵐ[boundarySurfaceMeasure Ω] T u + T v) ∧
      (∀ (a : ℝ) u, T (a • u) =ᵐ[boundarySurfaceMeasure Ω] a • T u) ∧
      (∀ g h, IsBesov Ω (1 - 1 / p) p g → IsBesov Ω (1 - 1 / p) p h → E (g + h) = E g + E h) ∧
      (∀ (a : ℝ) g, IsBesov Ω (1 - 1 / p) p g → E (a • g) = a • E g) ∧
      (∀ g, IsBesov Ω (1 - 1 / p) p g →
        w1pNorm Ω p (E g) ≤ (C : ℝ≥0∞) * besovNorm Ω (1 - 1 / p) p g ∧
        T (E g) =ᵐ[boundarySurfaceMeasure Ω] g) := by
  obtain ⟨C₁, hC₁⟩ := hTI
  obtain ⟨C₂, E, hEadd, hEsmul, hE⟩ := hRI
  choose T hT using fun u => (hC₁ u).1
  refine ⟨max C₁ C₂, T, E, fun u => ⟨hT u, ⟨?_, ?_⟩, ?_⟩, fun u v => ?_, fun a u => ?_, hEadd,
    hEsmul, fun g hg => ⟨(hE g hg).2.trans ?_, ?_⟩⟩
  · exact (hT u).1.aestronglyMeasurable.aemeasurable
  · exact ((hC₁ u).2.2 _ (hT u)).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (w1pNorm_lt_top u))
  · refine ((hC₁ u).2.2 _ (hT u)).trans ?_
    gcongr
    exact le_max_left _ _
  · exact (hC₁ (u + v)).2.1 _ _ (hT (u + v)) (IsTraceOf.add hΩo hp (hT u) (hT v))
  · exact (hC₁ (a • u)).2.1 _ _ (hT (a • u)) (IsTraceOf.smul hΩo (hT u) a)
  · gcongr
    exact le_max_right _ _
  · exact (hC₁ (E g)).2.1 _ _ (hT (E g)) (hE g hg).1

end PDE.TraceLane
