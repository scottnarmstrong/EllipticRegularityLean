module

public import EllipticRegularity.Schauder.OneDimensionalContinuous

/-! # The continuous-coefficient Schauder estimate in dimension one

This is the exact one-dimensional specialization of the source-facing
continuous-coefficient estimate. In one dimension the constant-flux argument
gives a bound independent of the supplied coefficient modulus.
-/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The exact continuous-coefficient Schauder estimate specialized to
dimension one. -/
theorem exists_continuousCoefficientCalpha_constant_oneDimensional
    (_hd : 0 < (1 : ℕ)) {Λ : ℝ}
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ω : ℝ → ℝ) (_hω0 : ω 0 = 0)
    (_hωnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ ω t)
    (_hωlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField 1,
      ContinuousOn a (euclideanClosedBall (0 : Vec 1) 1) →
      (∀ x ∈ euclideanClosedBall (0 : Vec 1) 1,
        IsEllipticMatrix 1 Λ (a x)) →
      (∀ x ∈ euclideanClosedBall (0 : Vec 1) 1,
        ∀ y ∈ euclideanClosedBall (0 : Vec 1) 1,
        IsMatrixPerturbationLE (ω (vecEuclideanNorm (x - y))) (a x) (a y)) →
      ∀ u : H1Function (euclideanBall (0 : Vec 1) 1),
      ∀ F : Vec 1 → Vec 1,
      (∀ i : Fin 1, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec 1) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal ((1 : ℝ) / (1 - α)))
        (volumeOn (euclideanBall (0 : Vec 1) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 1) 1) u 0 F →
      HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec 1) (1 / 2))
        u.toFun α
        ((C / α) *
          (Real.sqrt (∫ x in euclideanBall (0 : Vec 1) 1,
            vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec 1) 1)
            (ENNReal.ofReal ((1 : ℝ) / (1 - α))) F hF / (1 - α))) := by
  let C : ℝ := 32 * (1 + |Λ|)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a ha hell _hmod u F hFmeas hF hsol
  have hopenClosed : euclideanBall (0 : Vec 1) 1 ⊆
      euclideanClosedBall (0 : Vec 1) 1 :=
    euclideanBall_subset_euclideanClosedBall _ _
  have haEntry : ∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec 1) 1)) := by
    intro i j
    have hcont : ContinuousOn (fun x => a x i j)
        (euclideanClosedBall (0 : Vec 1) 1) :=
      continuousOn_pi.mp (continuousOn_pi.mp ha i) j
    have hclosed : AEStronglyMeasurable (fun x => a x i j)
        (volumeOn (euclideanClosedBall (0 : Vec 1) 1)) :=
      hcont.aestronglyMeasurable (measurableSet_euclideanClosedBall _ _)
    exact (hclosed.mono_measure
      (Measure.restrict_mono hopenClosed le_rfl)).aemeasurable
  have hellOpen : ∀ x ∈ euclideanBall (0 : Vec 1) 1,
      IsEllipticMatrix 1 Λ (a x) := fun x hx => hell x (hopenClosed hx)
  have hFcoord : AEStronglyMeasurable (fun x => F x 0)
      (volumeOn (euclideanBall (0 : Vec 1) 1)) := hFmeas 0
  have h := schauder_oneDimensional_continuous hα0 hα1 u haEntry hellOpen
    hFcoord hF hsol
  have hnorm : euclideanFieldLpNormOn (euclideanBall (0 : Vec 1) 1)
      (ENNReal.ofReal ((1 : ℝ) / (1 - α))) F hF =
      (euclideanFieldELpNormOn (euclideanBall (0 : Vec 1) 1)
        (ENNReal.ofReal ((1 : ℝ) / (1 - α))) F).toReal := by
    unfold euclideanFieldLpNormOn euclideanFieldELpNormOn
    exact lpNormOn_eq_toReal _ _ _ hF
  simpa only [C, hnorm] using h

end

end PDE
