module

public import PDEFoundation.Geometry.PlanarBlockRotation
public import PDEFoundation.Measure.VecAppendZeroBlock

/-! # Cancellation of planar block odd functions -/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- A function of the first planar block that changes sign under the quarter
turn has zero average on every centered round ball. -/
theorem integral_planarBlockOdd_normalizedVolumeOn_ball_eq_zero
    (n : ℕ) {R : ℝ} (hR : 0 < R) (f : Vec 2 → ℝ)
    (hf : Integrable
      (fun z : Vec (2 + n) => f (vecAppendEquiv 2 n z).1)
      (normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R)))
    (hodd : ∀ x : Vec 2, x ≠ 0 → f (planarQuarterTurn x) = -f x) :
    ∫ z : Vec (2 + n), f (vecAppendEquiv 2 n z).1
      ∂(normalizedVolumeOn (euclideanBall (0 : Vec (2 + n)) R)) = 0 := by
  let B := euclideanBall (0 : Vec (2 + n)) R
  let μ := normalizedVolumeOn B
  let g : Vec (2 + n) → ℝ := fun z => f (vecAppendEquiv 2 n z).1
  have hneRestr : ∀ᵐ z ∂volume.restrict B,
      (vecAppendEquiv 2 n z).1 ≠ 0 :=
    ae_vecAppendEquiv_fst_ne_zero_restrict (n := n) (by omega) B
  have hne : ∀ᵐ z ∂μ, (vecAppendEquiv 2 n z).1 ≠ 0 := by
    exact Measure.ae_smul_measure hneRestr (volume B)⁻¹
  have hcomp : (fun z => g (planarBlockRotation n z)) =ᵐ[μ] fun z => -g z := by
    filter_upwards [hne] with z hz
    simpa only [g, vecAppendEquiv_planarBlockRotation_fst] using hodd _ hz
  have hmp : MeasurePreserving (planarBlockRotation n) μ μ :=
    measurePreserving_planarBlockRotation_normalizedVolumeOn_ball n hR
  have hMapAES : AEStronglyMeasurable g (Measure.map (planarBlockRotation n) μ) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  have hChange := integral_map hmp.aemeasurable hMapAES
  rw [hmp.map_eq] at hChange
  have hint : (∫ z, g z ∂μ) = -(∫ z, g z ∂μ) := by
    calc
      ∫ z, g z ∂μ = ∫ z, g (planarBlockRotation n z) ∂μ :=
        hChange
      _ = ∫ z, -g z ∂μ := integral_congr_ae hcomp
      _ = -(∫ z, g z ∂μ) := integral_neg g
  have : ∫ z, g z ∂μ = 0 := by linarith
  exact this

end

end PDE
