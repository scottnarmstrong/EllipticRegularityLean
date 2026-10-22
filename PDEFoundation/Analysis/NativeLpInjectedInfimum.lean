module

public import PDEFoundation.Analysis.NativeLpInjectedMinimality

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Exact norm attainment and infimum for an injective conjugate-`Lᵖ`
embedding, under its induced norm. This generic helper assumes the embedding's
injectivity; Sobolev consumers must prove it internally. -/
theorem exists_nativeLp_density_and_infimum_through_injective
    [IsFiniteMeasure μ] {d : ℕ} {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (p / (p - 1)))]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ]
      Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ)
    (hA : Function.Injective A) :
    letI : NormedAddCommGroup E :=
      NormedAddCommGroup.induced E
        (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A hA
    letI : NormedSpace ℝ E :=
      NormedSpace.induced ℝ E
        (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A
    ∀ L : E →L[ℝ] ℝ, ∃ F : α → Vec d,
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) ∧
      MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) μ ∧
      (∀ u : E, L u = -∫ x, vecDot (F x) ((A u x).toVec) ∂μ) ∧
      (eLpNorm (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal p) μ).toReal = ‖L‖ ∧
      ‖L‖ = sInf {N : ℝ | ∃ G : α → Vec d,
        (∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) μ) ∧
        MemLp (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) μ ∧
        (∀ u : E, L u = -∫ x, vecDot (G x) ((A u x).toVec) ∂μ) ∧
        (eLpNorm (fun x => vecEuclideanNorm (G x))
          (ENNReal.ofReal p) μ).toReal = N} := by
  let : NormedAddCommGroup E :=
    NormedAddCommGroup.induced E
      (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A hA
  let : NormedSpace ℝ E :=
    NormedSpace.induced ℝ E
      (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A
  intro L
  rcases exists_nativeLp_density_through_injective hp A hA L with
    ⟨F, hFm, hFLp, hFrep, hFnorm⟩
  have hlower (N : ℝ) (hN : ∃ G : α → Vec d,
      (∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) μ) ∧
      MemLp (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) μ ∧
      (∀ u : E, L u = -∫ x, vecDot (G x) ((A u x).toVec) ∂μ) ∧
      (eLpNorm (fun x => vecEuclideanNorm (G x))
        (ENNReal.ofReal p) μ).toReal = N) : ‖L‖ ≤ N := by
    rcases hN with ⟨G, hGm, hGLp, hGrep, hGnorm⟩
    rw [← hGnorm]
    exact norm_le_nativeLp_density_of_represents_injective hp A hA L G
      hGm hGLp hGrep
  refine ⟨F, hFm, hFLp, hFrep, hFnorm, ?_⟩
  apply le_antisymm
  · refine le_csInf ?_ hlower
    exact ⟨‖L‖, F, hFm, hFLp, hFrep, hFnorm⟩
  · apply csInf_le ⟨‖L‖, hlower⟩
    exact ⟨F, hFm, hFLp, hFrep, hFnorm⟩

end

end PDE
