module

public import EllipticRegularity.DeGiorgi.LevelSetRecurrence

/-!
# The endpoint of the De Giorgi level-set iteration

This module turns decay of the nested positive-part energies into an almost-
everywhere upper bound on the limiting ball.  The argument compares the fixed
final excess directly with every member of the energy sequence, so it does not
require a moving-domain convergence theorem.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Topology

/-- If the nested De Giorgi positive-part energies tend to zero, then the
limiting truncation is zero almost everywhere on the limiting ball.  This is
an almost-everywhere statement about the Sobolev representative; a pointwise
bound requires a later continuous representative. -/
theorem ae_le_add_of_tendsto_deGiorgiLevelSetEnergy_zero
    {d : ℕ} {r R k₀ K : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {u : H1Function U}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hK : 0 < K)
    (hY : Tendsto (deGiorgiLevelSetEnergy u x₀ r R k₀ K) atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), u x ≤ k₀ + K := by
  let finalExcess : Vec d → ℝ := fun x => max (u x - (k₀ + K)) 0
  let finalEnergy : ℝ :=
    ∫ x in euclideanBall x₀ r, finalExcess x ^ 2
  have hfinalBallU : euclideanBall x₀ r ⊆ U :=
    (euclideanBall_mono hr.le hrR.le).trans hball
  have hfinalL2 : MemLp finalExcess 2
      (volume.restrict (euclideanBall x₀ r)) := by
    simpa only [finalExcess, H1Function.positivePartSubConst_toFun] using
      memLpOn_mono hfinalBallU (u.positivePartSubConst hU (k₀ + K)).memL2
  have hfinalSqInt : Integrable (fun x => finalExcess x ^ 2)
      (volume.restrict (euclideanBall x₀ r)) := by
    simpa only [pow_two] using! integrableOn_mul_of_memL2On hfinalL2 hfinalL2
  have hfinal_le_energy :
      ∀ n, finalEnergy ≤ deGiorgiLevelSetEnergy u x₀ r R k₀ K n := by
    intro n
    let rn : ℝ := deGiorgiRadius r R n
    let kn : ℝ := k₀ + deGiorgiLevel K n
    let wn : Vec d → ℝ := fun x => max (u x - kn) 0
    have hrn_pos : 0 < rn := by
      dsimp only [rn]
      exact deGiorgiRadius_pos hr hrR n
    have hballnU : euclideanBall x₀ rn ⊆ U := by
      dsimp only [rn]
      exact (euclideanBall_deGiorgiRadius_subset hr hrR n).trans hball
    have hfinal_subset_balln : euclideanBall x₀ r ⊆ euclideanBall x₀ rn := by
      apply euclideanBall_mono hr.le
      dsimp only [rn]
      exact (deGiorgiRadius_lower_lt hrR n).le
    have hkn_le : kn ≤ k₀ + K := by
      dsimp only [kn]
      linarith [deGiorgiLevel_lt hK n]
    have hwnL2 : MemLp wn 2 (volume.restrict (euclideanBall x₀ rn)) := by
      simpa only [wn, H1Function.positivePartSubConst_toFun] using
        memLpOn_mono hballnU (u.positivePartSubConst hU kn).memL2
    have hwnSqInt : Integrable (fun x => wn x ^ 2)
        (volume.restrict (euclideanBall x₀ rn)) := by
      simpa only [pow_two] using! integrableOn_mul_of_memL2On hwnL2 hwnL2
    have hwnSqIntInner : Integrable (fun x => wn x ^ 2)
        (volume.restrict (euclideanBall x₀ r)) :=
      hwnSqInt.mono_measure (Measure.restrict_mono hfinal_subset_balln le_rfl)
    have hfinal_le_wn :
        (∫ x in euclideanBall x₀ r, finalExcess x ^ 2) ≤
          ∫ x in euclideanBall x₀ r, wn x ^ 2 := by
      apply integral_mono_ae hfinalSqInt hwnSqIntInner
      exact Filter.Eventually.of_forall fun x => by
        have hexcess : finalExcess x ≤ wn x := by
          dsimp only [finalExcess, wn]
          apply max_le_max_right
          linarith
        have hfinal_nonneg : 0 ≤ finalExcess x := by
          dsimp only [finalExcess]
          exact le_max_right _ _
        have hwn_nonneg : 0 ≤ wn x := by
          dsimp only [wn]
          exact le_max_right _ _
        nlinarith
    have hinnner_le_outer :
        (∫ x in euclideanBall x₀ r, wn x ^ 2) ≤
          ∫ x in euclideanBall x₀ rn, wn x ^ 2 := by
      apply MeasureTheory.setIntegral_mono_set hwnSqInt
      · exact Filter.Eventually.of_forall fun x => sq_nonneg (wn x)
      · exact Filter.Eventually.of_forall fun x hx => hfinal_subset_balln hx
    calc
      finalEnergy = ∫ x in euclideanBall x₀ r, finalExcess x ^ 2 := rfl
      _ ≤ ∫ x in euclideanBall x₀ r, wn x ^ 2 := hfinal_le_wn
      _ ≤ ∫ x in euclideanBall x₀ rn, wn x ^ 2 := hinnner_le_outer
      _ = deGiorgiLevelSetEnergy u x₀ r R k₀ K n := by
        rfl
  have hfinal_nonneg : 0 ≤ finalEnergy := by
    dsimp only [finalEnergy]
    exact integral_nonneg fun x => sq_nonneg (finalExcess x)
  have hfinal_le_zero : finalEnergy ≤ 0 := by
    apply ge_of_tendsto hY
    exact Filter.Eventually.of_forall hfinal_le_energy
  have hfinal_eq_zero : finalEnergy = 0 :=
    le_antisymm hfinal_le_zero hfinal_nonneg
  have hfinalSq_ae_zero : (fun x => finalExcess x ^ 2) =ᵐ[
      volume.restrict (euclideanBall x₀ r)] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg (finalExcess x)) hfinalSqInt).mp
    simpa only [finalEnergy] using hfinal_eq_zero
  filter_upwards [hfinalSq_ae_zero] with x hx
  have hfinal_zero : finalExcess x = 0 := by
    apply sq_eq_zero_iff.mp
    simpa using hx
  change max (u x - (k₀ + K)) 0 = 0 at hfinal_zero
  exact sub_nonpos.mp (max_eq_right_iff.mp hfinal_zero)

end PDE
