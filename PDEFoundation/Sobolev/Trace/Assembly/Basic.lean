module

public import PDEFoundation.Sobolev.Trace.Defs
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-!
# Basic facts for the trace assembly

The surface measure `σ = boundarySurfaceMeasure Ω` is carried by `frontier Ω`, so functions
continuous on `closure Ω` are `σ`-a.e. strongly measurable.  The `W^{1,p}` pair norm satisfies the
triangle inequality, and the classical gradient is additive at points of the open set `Ω` for
functions in `C¹(Ω̄)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Set (Vec d)}

/-- The surface measure does not charge the complement of the frontier. -/
theorem boundarySurfaceMeasure_compl_frontier :
    boundarySurfaceMeasure Ω (frontier Ω)ᶜ = 0 := by
  unfold boundarySurfaceMeasure
  rw [Measure.map_apply (show Measurable (HilbertVec.toVec (d := d)) from (MeasurableEquiv.toLp 2 (Vec d)).symm.measurable) isClosed_frontier.measurableSet.compl,
    Measure.restrict_apply ((show Measurable (HilbertVec.toVec (d := d)) from (MeasurableEquiv.toLp 2 (Vec d)).symm.measurable) isClosed_frontier.measurableSet.compl)]
  convert measure_empty (μ := (μHE[d - 1] : Measure (HilbertVec d)))
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_image, mem_empty_iff_false,
    iff_false, not_and]
  rintro hy ⟨x, hx, rfl⟩
  exact hy hx

theorem boundarySurfaceMeasure_restrict_frontier :
    (boundarySurfaceMeasure Ω).restrict (frontier Ω) = boundarySurfaceMeasure Ω :=
  Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1
    boundarySurfaceMeasure_compl_frontier |>.mono fun _ h => by simpa using h)

/-- Functions continuous on `closure Ω` are `σ`-a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_continuousOn_closure {φ : Vec d → ℝ}
    (hφ : ContinuousOn φ (closure Ω)) : AEStronglyMeasurable φ (boundarySurfaceMeasure Ω) := by
  rw [← boundarySurfaceMeasure_restrict_frontier]
  exact (hφ.mono frontier_subset_closure).aestronglyMeasurable isClosed_frontier.measurableSet

/-- At points of the open set `Ω`, the classical gradient is additive on `C¹(Ω̄)`. -/
theorem classicalGradient_sub_of_mem (hΩo : IsOpen Ω) {φ ψ : Vec d → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (closure Ω)) (hψ : ContDiffOn ℝ 1 ψ (closure Ω)) {x : Vec d}
    (hx : x ∈ Ω) :
    classicalGradient (φ - ψ) x = classicalGradient φ x - classicalGradient ψ x := by
  have hn : closure Ω ∈ 𝓝 x := mem_of_superset (hΩo.mem_nhds hx) subset_closure
  have h1 : DifferentiableAt ℝ φ x :=
    ((hφ.differentiableOn one_ne_zero) x (subset_closure hx)).differentiableAt hn
  have h2 : DifferentiableAt ℝ ψ x :=
    ((hψ.differentiableOn one_ne_zero) x (subset_closure hx)).differentiableAt hn
  funext i
  simp [classicalGradient, fderiv_sub h1 h2]

/-- The classical gradient of a `C¹(Ω̄)` function is measurable on `Ω`. -/
theorem aestronglyMeasurable_classicalGradient (hΩo : IsOpen Ω) {φ : Vec d → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (closure Ω)) :
    AEStronglyMeasurable (classicalGradient φ) (volumeOn Ω) := by
  have hcont : ContinuousOn (fderiv ℝ φ) Ω :=
    (hφ.mono subset_closure).continuousOn_fderiv_of_isOpen hΩo le_rfl
  have hg : ContinuousOn (classicalGradient φ) Ω := by
    refine continuousOn_pi.2 fun i => ?_
    exact hcont.clm_apply continuousOn_const
  exact hg.aestronglyMeasurable hΩo.measurableSet

theorem aestronglyMeasurable_of_contDiffOn_closure (hΩo : IsOpen Ω) {φ : Vec d → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (closure Ω)) : AEStronglyMeasurable φ (volumeOn Ω) :=
  (hφ.continuousOn.mono subset_closure).aestronglyMeasurable hΩo.measurableSet

/-- Triangle inequality for the `W^{1,p}` pair norm. -/
theorem w1pPairNorm_add_le {p : ℝ} (hp : 1 ≤ p) (f g : Vec d → ℝ) {F G : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (volumeOn Ω)) (hG : AEStronglyMeasurable G (volumeOn Ω)) :
    w1pPairNorm Ω p (f + g) (F + G) ≤ w1pPairNorm Ω p f F + w1pPairNorm Ω p g G := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  unfold w1pPairNorm
  have h1 := eLpNorm_add_le (μ := volumeOn Ω) hp1 (f := f) (g := g)
  have h2 : eLpNorm (fun x => vecEuclideanNorm ((F + G) x)) (ENNReal.ofReal p) (volumeOn Ω) ≤
      eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn Ω) +
        eLpNorm (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) (volumeOn Ω) := by
    refine (eLpNorm_mono (g := (fun x => vecEuclideanNorm (F x)) + fun x => vecEuclideanNorm (G x))
      (continuous_vecEuclideanNorm.comp_aestronglyMeasurable (hF.add hG)) fun x => ?_).trans (eLpNorm_add_le (μ := volumeOn Ω) hp1 (f := fun x => vecEuclideanNorm (F x)) (g := fun x => vecEuclideanNorm (G x)))
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (vecEuclideanNorm_nonneg _), abs_of_nonneg (add_nonneg
      (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _))]
    exact vecEuclideanNorm_add_le _ _
  calc _ ≤ (eLpNorm f (ENNReal.ofReal p) (volumeOn Ω) + eLpNorm g (ENNReal.ofReal p) (volumeOn Ω)) +
        (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn Ω) +
          eLpNorm (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) (volumeOn Ω)) :=
        add_le_add h1 h2
    _ = _ := by ring

theorem w1pPairNorm_neg {p : ℝ} (f : Vec d → ℝ) (F : Vec d → Vec d) :
    w1pPairNorm Ω p (-f) (-F) = w1pPairNorm Ω p f F := by
  unfold w1pPairNorm
  rw [eLpNorm_neg]
  congr 2
  funext x
  exact vecEuclideanNorm_neg _

theorem w1pPairNorm_sub_le {p : ℝ} (hp : 1 ≤ p) (f g : Vec d → ℝ) {F G : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (volumeOn Ω)) (hG : AEStronglyMeasurable G (volumeOn Ω)) :
    w1pPairNorm Ω p (f - g) (F - G) ≤ w1pPairNorm Ω p f F + w1pPairNorm Ω p g G := by
  rw [sub_eq_add_neg f g, sub_eq_add_neg F G, ← w1pPairNorm_neg (Ω := Ω) (p := p) g G]
  exact w1pPairNorm_add_le hp f (-g) hF hG.neg

/-- Congruence of the pair norm under a.e. equality on `Ω`. -/
theorem w1pPairNorm_congr_ae {p : ℝ} {f g : Vec d → ℝ} {F G : Vec d → Vec d}
    (hfg : f =ᵐ[volumeOn Ω] g) (hFG : F =ᵐ[volumeOn Ω] G) :
    w1pPairNorm Ω p f F = w1pPairNorm Ω p g G := by
  unfold w1pPairNorm
  rw [eLpNorm_congr_ae hfg]
  congr 1
  exact eLpNorm_congr_ae (hFG.mono fun x hx => by simp only [hx])

/-- The `W^{1,p}` norm of an element is finite. -/
theorem w1pNorm_lt_top {p : ℝ} (u : W1pFunction Ω (ENNReal.ofReal p)) : w1pNorm Ω p u < ⊤ := by
  unfold w1pNorm w1pPairNorm
  exact ENNReal.add_lt_top.2 ⟨u.memLp.eLpNorm_lt_top,
    (GradMemLpOn.memLp_vecEuclideanNorm u.gradMemLp).eLpNorm_lt_top⟩

theorem aestronglyMeasurable_w1p_grad {p : ℝ} (u : W1pFunction Ω (ENNReal.ofReal p)) :
    AEStronglyMeasurable u.grad (volumeOn Ω) :=
  (aemeasurable_pi_iff.2 fun i => (u.gradMemLp i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable

end PDE.TraceLane
