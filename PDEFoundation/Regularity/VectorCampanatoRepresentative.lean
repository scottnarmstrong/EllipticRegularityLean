module

public import PDEFoundation.Regularity.VectorBallCampanato

/-!
# Canonical vector Campanato representatives

The representative is assembled coordinatewise from dyadic centered-cube
averages of the zero extension from the unit Euclidean ball.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The canonical vector representative obtained from the coordinatewise
dyadic representatives of the zero extension from the unit ball. -/
def vectorCampanatoRepresentative
    (r₀ : ℝ) (g : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => dyadicCenteredCubeRepresentative
    (fun y => (euclideanBall (0 : Vec d) 1).indicator g y i)
    (vectorBallCampanatoBaseRadius d r₀) x

private theorem centeredCubeL2Oscillation_congr_ae'
    {f h : Vec d → ℝ} {z : Vec d} {r : ℝ}
    (hfh : f =ᵐ[volumeOn (centeredAxisCube z r)] h) :
    centeredCubeL2Oscillation f z r =
      centeredCubeL2Oscillation h z r := by
  have hmean : centeredCubeAverage f z r = centeredCubeAverage h z r :=
    integralAverage_congr_ae hfh
  have hfhNorm : f =ᵐ[normalizedVolumeOn (centeredAxisCube z r)] h := by
    unfold normalizedVolumeOn
    exact MeasureTheory.Measure.ae_smul_measure hfh _
  unfold centeredCubeL2Oscillation
  rw [hmean]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfhNorm] with x hx
  rw [hx]

private theorem centeredAxisCube_vectorBallBase_subset_unit'
    (hd : 0 < d) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    {z : Vec d} (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) :
    centeredAxisCube z (vectorBallCampanatoBaseRadius d r₀) ⊆
      euclideanBall (0 : Vec d) 1 := by
  have hroot : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hR := vectorBallCampanatoBaseRadius_pos hd hr₀
  have hcube := centeredAxisCube_subset_euclideanBall hd z hR
  have heq : 2 * Real.sqrt d * vectorBallCampanatoBaseRadius d r₀ = r₀ := by
    unfold vectorBallCampanatoBaseRadius
    field_simp
  rw [heq] at hcube
  exact hcube.trans ((euclideanBall_mono hr₀.le
    (hr₀le.trans (by norm_num))).trans
      (euclideanBall_half_subset_unit_of_center_mem_half hz))

/-- A vector field with interior centered mean decay has a canonical
coordinatewise Campanato representative which agrees almost everywhere on
the half ball and satisfies the local Euclidean vector Hölder bound. -/
theorem exists_vectorCampanatoRepresentative_of_vectorBallScale
    (hd : 0 < d) {r₀ α K : ℝ} (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) 1) g)
    (hscale : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
        centeredVectorMeanL2 (euclideanBall z r) g ≤ K * r ^ α) :
    ∃ G : Vec d → Vec d,
      G = vectorCampanatoRepresentative r₀ g ∧
      G =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] g ∧
      ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
        ∀ y ∈ euclideanBall (0 : Vec d) (1 / 2),
          vecEuclideanNorm (x - y) ≤
              vectorBallCampanatoBaseRadius d r₀ / 2 →
            vecEuclideanNorm (G x - G y) ≤
              ((d : ℝ) * dyadicCampanatoHolderConst d α *
                vectorBallCampanatoCoefficient d * K) *
                vecEuclideanNorm (x - y) ^ α := by
  let U := euclideanBall (0 : Vec d) 1
  let S := euclideanBall (0 : Vec d) (1 / 2)
  let R := vectorBallCampanatoBaseRadius d r₀
  let G := vectorCampanatoRepresentative r₀ g
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (isOpen_euclideanBall _ _).measurableSet
  have hR : 0 < R := by
    dsimp [R]
    exact vectorBallCampanatoBaseRadius_pos hd hr₀
  have hSU : S ⊆ U := by
    dsimp [S, U]
    exact euclideanBall_mono (by norm_num) (by norm_num)
  let ge : Vec d → Vec d := U.indicator g
  have hgeL2 (i : Fin d) : MemLp (fun x => ge x i) 2 volume := by
    have hi : (fun x => ge x i) = U.indicator (fun x => g x i) := by
      funext x
      by_cases hx : x ∈ U <;> simp [ge, hx]
    rw [hi, memLp_indicator_iff_restrict hUmeas]
    exact hg i
  have hgeLoc (i : Fin d) : LocallyIntegrable (fun x => ge x i) volume :=
    (hgeL2 i).locallyIntegrable (by norm_num)
  have hgeSqInt (i : Fin d) : Integrable (fun x => (ge x i) ^ 2) volume := by
    simpa only [pow_two] using! (hgeL2 i).integrable_mul (hgeL2 i)
  have hgeSqLoc (i : Fin d) :
      LocallyIntegrable (fun x => (ge x i) ^ 2) volume :=
    (hgeSqInt i).locallyIntegrable
  have hcampG (i : Fin d) :
      DyadicCenteredCubeCampanatoBoundOn (fun x => ge x i) S R α
        (vectorBallCampanatoCoefficient d * K) := by
    have hcamp :=
      dyadicCenteredCubeCampanatoBoundOn_coordinate_of_vectorBallScale
        hd hr₀ hr₀le hα0 hα1 hK hg hscale i
    intro z hz n
    let r := dyadicRadius R n
    have hr : 0 < r := dyadicRadius_pos hR n
    have hrle : r ≤ R := dyadicRadius_le hR.le n
    have hcubeBase : centeredAxisCube z R ⊆ U := by
      dsimp [R, U, S] at hz ⊢
      exact centeredAxisCube_vectorBallBase_subset_unit' hd hr₀ hr₀le hz
    have hcube : centeredAxisCube z r ⊆ U :=
      (centeredAxisCube_mono z hrle).trans hcubeBase
    have heq : (fun x => ge x i) =ᵐ[volumeOn (centeredAxisCube z r)]
        (fun x => g x i) := by
      filter_upwards
        [ae_restrict_mem (isOpen_centeredAxisCube z r).measurableSet]
        with x hx
      simp [ge, hcube hx]
    have hosc := centeredCubeL2Oscillation_congr_ae' heq
    change centeredCubeL2Oscillation (fun x => ge x i) z r ≤
      (vectorBallCampanatoCoefficient d * K) * r ^ α
    rw [hosc]
    simpa only [R, r, dyadicRadius] using hcamp z hz n
  have hrepCoord (i : Fin d) :
      (fun x => G x i) =ᵐ[volume] (fun x => ge x i) := by
    dsimp [G, vectorCampanatoRepresentative, R]
    exact dyadicCenteredCubeRepresentative_ae_eq (hgeLoc i) hR
  have hrepS : G =ᵐ[volumeOn S] g := by
    have hall : ∀ᵐ x ∂volume, ∀ i, G x i = ge x i :=
      ae_all_iff.mpr hrepCoord
    have hallS : ∀ᵐ x ∂volumeOn S, ∀ i, G x i = ge x i :=
      hall.filter_mono
        (ae_mono (Measure.restrict_le_self (μ := volume) (s := S)))
    filter_upwards [hallS, ae_restrict_mem (by
      dsimp [S]
      exact (isOpen_euclideanBall _ _).measurableSet)] with x hxi hx
    funext i
    rw [hxi i]
    simp [ge, hSU hx]
  refine ⟨G, rfl, ?_, ?_⟩
  · simpa only [S] using hrepS
  · intro x hx y hy hxy
    have hsup : ‖x - y‖ ≤ R / 2 :=
      (norm_le_vecEuclideanNorm (x - y)).trans hxy
    have hcoord (i : Fin d) :
        |G x i - G y i| ≤
          (dyadicCampanatoHolderConst d α *
            (vectorBallCampanatoCoefficient d * K)) *
            vecEuclideanNorm (x - y) ^ α := by
      have hi := (hcampG i).abs_representative_sub_le
        hα0 hR (mul_nonneg (by
          unfold vectorBallCampanatoCoefficient
          positivity) hK)
        (fun z _ => locallyIntegrable_integrableOn_centeredAxisCube
          (hgeLoc i) z hR)
        (fun z _ => locallyIntegrable_integrableOn_centeredAxisCube
          (hgeSqLoc i) z hR)
        hx hy hsup
      have hpow := Real.rpow_le_rpow (norm_nonneg (x - y))
        (norm_le_vecEuclideanNorm (x - y)) hα0.le
      exact hi.trans (mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (dyadicCampanatoHolderConst_nonneg d hα0)
          (mul_nonneg (by
            unfold vectorBallCampanatoCoefficient
            positivity) hK)))
    calc
      vecEuclideanNorm (G x - G y) ≤
          ∑ i : Fin d, |G x i - G y i| :=
        vecEuclideanNorm_le_sum_abs (G x - G y)
      _ ≤ ∑ _i : Fin d,
          (dyadicCampanatoHolderConst d α *
            (vectorBallCampanatoCoefficient d * K)) *
            vecEuclideanNorm (x - y) ^ α :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = ((d : ℝ) * dyadicCampanatoHolderConst d α *
          vectorBallCampanatoCoefficient d * K) *
          vecEuclideanNorm (x - y) ^ α := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

end

end PDE
