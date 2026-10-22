module

public import PDEFoundation.Regularity.EssentialOscillationHolder

/-!
# Proof of `PDE.exists_holderRepresentative_of_essOsc_decay` (Lemma 1.20)

Hölder continuity from decay of the essential oscillation on cubes.
-/

@[expose] public section

namespace PDE.OscillationHolderProof

open MeasureTheory

/-- Essential oscillation decay on every centered cube gives a Hölder
representative on a smaller closed cube. -/
theorem result
    (d : ℕ) {α K R : ℝ} (x₀ : Vec d)
    (hα : 0 < α) (_hα₁ : α ≤ 1) (hK : 0 ≤ K) (hR : 0 < R)
    (u : Vec d → ℝ) (hu : IntegrableOn u (centeredAxisCube x₀ R))
    (hosc : ∀ (x : Vec d) (r : ℝ), 0 < r →
      centeredAxisCube x r ⊆ centeredAxisCube x₀ R →
      ∃ a b : ℝ,
        (∀ᵐ y ∂volumeOn (centeredAxisCube x r), u y ∈ Set.Icc a b) ∧
        b - a ≤ K * r ^ α) :
    ∃ v : Vec d → ℝ,
      (∀ᵐ y ∂volumeOn (closedCenteredAxisCube x₀ (R / 8)), v y = u y) ∧
      ∀ x ∈ closedCenteredAxisCube x₀ (R / 8),
        ∀ y ∈ closedCenteredAxisCube x₀ (R / 8),
          |v x - v y| ≤ 2 ^ α * K * vecEuclideanNorm (x - y) ^ α := by
  let U := centeredAxisCube x₀ R
  let g : Vec d → ℝ := Set.indicator U u
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (isOpen_centeredAxisCube x₀ R).measurableSet
  have hgInt : Integrable g volume := by
    dsimp [g]
    exact hu.integrable_indicator hUmeas
  have hgLocal : LocallyIntegrable g volume := hgInt.locallyIntegrable
  have hdecay : CenteredCubeEssentialOscillationDecayOn g U α K := by
    intro x r hr hsub
    obtain ⟨a, b, hRange, hab⟩ := hosc x r hr hsub
    refine ⟨a, b, ?_, hab⟩
    filter_upwards [hRange,
      ae_restrict_mem (isOpen_centeredAxisCube x r).measurableSet] with y hy hys
    simpa only [g, Set.indicator_of_mem (hsub hys)] using hy
  have hrep :=
    hdecay.hasEuclideanHolderRepresentativeOn_closed_inner hR hα hK hgLocal
  rcases hrep with ⟨v, hvEq, hvHolder⟩
  have hVsub : closedCenteredAxisCube x₀ (R / 8) ⊆ U := by
    intro y hy i _
    have hcoord := hy i (Set.mem_univ i)
    change x₀ i - R / 8 ≤ y i ∧ y i ≤ x₀ i + R / 8 at hcoord
    change x₀ i - R < y i ∧ y i < x₀ i + R
    constructor <;> linarith [hR]
  have hExtEq : g =ᵐ[volumeOn (closedCenteredAxisCube x₀ (R / 8))] u := by
    filter_upwards [ae_restrict_mem
      (isClosed_closedCenteredAxisCube x₀ (R / 8)).measurableSet] with y hy
    simp only [g, Set.indicator_of_mem (hVsub hy)]
  refine ⟨v, ?_, ?_⟩
  · exact hvEq.trans hExtEq
  · intro x hx y hy
    simpa only [mul_comm K ((2 : ℝ) ^ α)] using hvHolder x hx y hy

end PDE.OscillationHolderProof
