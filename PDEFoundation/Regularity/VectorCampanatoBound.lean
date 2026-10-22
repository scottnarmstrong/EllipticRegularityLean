module

public import PDEFoundation.Regularity.VectorCampanatoRepresentative

/-!
# Pointwise bounds for canonical vector Campanato representatives
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A uniform bound on all dyadic averages passes to the selected Campanato
representative. -/
theorem abs_dyadicCenteredCubeRepresentative_le_of_uniform_mean_bound
    {u : Vec d → ℝ} {S : Set (Vec d)} {R α K C : ℝ} {x : Vec d}
    (hα : 0 < α) (hR : 0 < R)
    (hu : IntegrableOn u (centeredAxisCube x R))
    (hu2 : IntegrableOn (fun z => u z ^ 2) (centeredAxisCube x R))
    (hcamp : DyadicCenteredCubeCampanatoBoundOn u S R α K)
    (hx : x ∈ S)
    (hmean : ∀ n : ℕ, |dyadicCenteredCubeMeanSeq u R x n| ≤ C) :
    |dyadicCenteredCubeRepresentative u R x| ≤ C := by
  apply le_of_tendsto
    (tendsto_dyadicCenteredCubeMeanSeq hα hR hu hu2 hcamp hx).abs
  exact Filter.Eventually.of_forall hmean

private theorem centeredCubeL2Oscillation_congr_ae''
    {f h : Vec d → ℝ} {z : Vec d} {r : ℝ}
    (hfh : f =ᵐ[volumeOn (centeredAxisCube z r)] h) :
    centeredCubeL2Oscillation f z r = centeredCubeL2Oscillation h z r := by
  have hmean : centeredCubeAverage f z r = centeredCubeAverage h z r :=
    integralAverage_congr_ae hfh
  have hfhNorm : f =ᵐ[normalizedVolumeOn (centeredAxisCube z r)] h := by
    unfold normalizedVolumeOn
    exact MeasureTheory.Measure.ae_smul_measure hfh _
  unfold centeredCubeL2Oscillation
  rw [hmean]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfhNorm] with y hy
  rw [hy]

/-- The canonical representative is pointwise bounded on the half unit ball
by the uniform uncentered vector mean energy on interior balls. -/
theorem vectorCampanatoRepresentative_pointwise_le_of_vectorBallEnergy
    (hd : 0 < d) {r₀ α K B : ℝ}
    (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (_hB : 0 ≤ B)
    {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) 1) g)
    (hscale : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
        centeredVectorMeanL2 (euclideanBall z r) g ≤ K * r ^ α)
    (henergy : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
        Real.sqrt (integralAverage (euclideanBall z r)
          (fun y => vecNormSq (g y))) ≤ B) :
    ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      vecEuclideanNorm (vectorCampanatoRepresentative r₀ g x) ≤
        (d : ℝ) *
          Real.sqrt ((Real.sqrt d) ^ d *
            (volume (euclideanBall (0 : Vec d) 1)).toReal) * B := by
  let U := euclideanBall (0 : Vec d) 1
  let S := euclideanBall (0 : Vec d) (1 / 2)
  let R := vectorBallCampanatoBaseRadius d r₀
  let ge : Vec d → Vec d := U.indicator g
  have hroot : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hR : 0 < R := by
    dsimp [R]
    exact vectorBallCampanatoBaseRadius_pos hd hr₀
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact (isOpen_euclideanBall _ _).measurableSet
  have hgeL2 (i : Fin d) : MemLp (fun y => ge y i) 2 volume := by
    have hi : (fun y => ge y i) = U.indicator (fun y => g y i) := by
      funext y
      by_cases hy : y ∈ U <;> simp [ge, hy]
    rw [hi, memLp_indicator_iff_restrict hUmeas]
    exact hg i
  have hgeLoc (i : Fin d) : LocallyIntegrable (fun y => ge y i) volume :=
    (hgeL2 i).locallyIntegrable (by norm_num)
  have hgeSqLoc (i : Fin d) :
      LocallyIntegrable (fun y => (ge y i) ^ 2) volume :=
    (by
      have : Integrable (fun y => (ge y i) ^ 2) volume := by
        simpa only [pow_two] using! (hgeL2 i).integrable_mul (hgeL2 i)
      exact this.locallyIntegrable)
  have hcampG (i : Fin d) :
      DyadicCenteredCubeCampanatoBoundOn (fun y => ge y i) S R α
        (vectorBallCampanatoCoefficient d * K) := by
    have hcamp :=
      dyadicCenteredCubeCampanatoBoundOn_coordinate_of_vectorBallScale
        hd hr₀ hr₀le hα0 hα1 hK hg hscale i
    intro z hz n
    let r := dyadicRadius R n
    have hr : 0 < r := dyadicRadius_pos hR n
    have hrle : r ≤ R := dyadicRadius_le hR.le n
    have hbaseBall : 2 * Real.sqrt d * R = r₀ := by
      dsimp [R, vectorBallCampanatoBaseRadius]
      field_simp
    have hrb : 2 * Real.sqrt d * r ≤ r₀ := by
      calc
        2 * Real.sqrt d * r ≤ 2 * Real.sqrt d * R :=
          mul_le_mul_of_nonneg_left hrle (by positivity)
        _ = r₀ := hbaseBall
    have hcube : centeredAxisCube z r ⊆ U := by
      have hc := centeredAxisCube_subset_euclideanBall hd z hr
      have hbsmall : euclideanBall z (2 * Real.sqrt d * r) ⊆
          euclideanBall z (1 / 2) :=
        euclideanBall_mono (by positivity)
          (hrb.trans (hr₀le.trans (by norm_num)))
      exact hc.trans (hbsmall.trans (by
        dsimp [S, U] at hz ⊢
        exact euclideanBall_half_subset_unit_of_center_mem_half hz))
    have heq : (fun y => ge y i) =ᵐ[volumeOn (centeredAxisCube z r)]
        (fun y => g y i) := by
      filter_upwards
        [ae_restrict_mem (isOpen_centeredAxisCube z r).measurableSet]
        with y hy
      simp [ge, hcube hy]
    change centeredCubeL2Oscillation (fun y => ge y i) z r ≤
      (vectorBallCampanatoCoefficient d * K) * r ^ α
    rw [centeredCubeL2Oscillation_congr_ae'' heq]
    simpa only [R, r, dyadicRadius] using hcamp z hz n
  intro x hx
  have hcoord (i : Fin d) :
      |vectorCampanatoRepresentative r₀ g x i| ≤
        Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) * B := by
    have hmean (n : ℕ) :
        |dyadicCenteredCubeMeanSeq (fun y => ge y i) R x n| ≤
          Real.sqrt ((Real.sqrt d) ^ d *
            (volume (euclideanBall (0 : Vec d) 1)).toReal) * B := by
      let r := dyadicRadius R n
      let rb := 2 * Real.sqrt d * r
      let Q := centeredAxisCube x r
      let D := euclideanBall x rb
      have hr : 0 < r := dyadicRadius_pos hR n
      have hrle : r ≤ R := dyadicRadius_le hR.le n
      have hrb : 0 < rb := by dsimp [rb]; positivity
      have hrb_le : rb ≤ r₀ := by
        dsimp [rb, R, vectorBallCampanatoBaseRadius] at hrle ⊢
        calc
          2 * Real.sqrt d * r ≤
              2 * Real.sqrt d * (r₀ / (2 * Real.sqrt d)) :=
            mul_le_mul_of_nonneg_left hrle (by positivity)
          _ = r₀ := by field_simp
      have hDU : D ⊆ U := by
        have hs : D ⊆ euclideanBall x (1 / 2) :=
          euclideanBall_mono hrb.le
            (hrb_le.trans (hr₀le.trans (by norm_num)))
        exact hs.trans (by
          dsimp [S, U] at hx ⊢
          exact euclideanBall_half_subset_unit_of_center_mem_half hx)
      have hQD : Q ⊆ D := by
        simpa only [Q, D, rb] using centeredAxisCube_subset_euclideanBall hd x hr
      have hgD : MemVectorL2On D g := fun j =>
        (hg j).mono_measure (Measure.restrict_mono hDU le_rfl)
      have hgQ : MemVectorL2On Q g := fun j =>
        (hgD j).mono_measure (Measure.restrict_mono hQD le_rfl)
      have hmeanEq : dyadicCenteredCubeMeanSeq (fun y => ge y i) R x n =
          vectorIntegralAverage Q g i := by
        unfold dyadicCenteredCubeMeanSeq centeredCubeAverage
        change integralAverage Q (fun y => ge y i) =
          vectorIntegralAverage Q g i
        have heq : (fun y => ge y i) =ᵐ[volumeOn Q] (fun y => g y i) := by
          filter_upwards [ae_restrict_mem (isOpen_centeredAxisCube x r).measurableSet]
            with y hy
          simp [ge, hDU (hQD hy)]
        rw [integralAverage_congr_ae heq, vectorIntegralAverage_apply]
      rw [hmeanEq]
      have havg := vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq
        hgQ (by simpa only [Q] using volume_centeredAxisCube_pos x hr)
        (lt_top_iff_ne_top.mpr (by
          simpa only [Q] using volume_centeredAxisCube_ne_top x r))
      have hrestrict := sqrt_integralAverage_vecNormSq_mono_set hQD
        (volume_euclideanBall_toReal_pos x hrb) hgD
      have hratio :
          Real.sqrt (volume D).toReal / Real.sqrt (volume Q).toReal =
            Real.sqrt ((Real.sqrt d) ^ d *
              (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
        simpa only [D, Q, rb] using sqrt_volume_enclosingBall_div_cube x hr hd
      rw [hratio] at hrestrict
      exact (abs_apply_le_vecEuclideanNorm (vectorIntegralAverage Q g) i).trans
        (havg.trans (hrestrict.trans (mul_le_mul_of_nonneg_left
          (henergy x hx rb hrb hrb_le) (Real.sqrt_nonneg _))))
    have hlim := abs_dyadicCenteredCubeRepresentative_le_of_uniform_mean_bound
      hα0 hR
      (locallyIntegrable_integrableOn_centeredAxisCube (hgeLoc i) x hR)
      (locallyIntegrable_integrableOn_centeredAxisCube (hgeSqLoc i) x hR)
      (hcampG i) hx hmean
    simpa only [vectorCampanatoRepresentative, U, R, ge] using hlim
  calc
    vecEuclideanNorm (vectorCampanatoRepresentative r₀ g x) ≤
        ∑ i : Fin d, |vectorCampanatoRepresentative r₀ g x i| :=
      vecEuclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin d,
        Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) * B :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end

end PDE
