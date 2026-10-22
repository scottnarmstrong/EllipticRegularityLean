module

public import PDEFoundation.Regularity.VectorCubeOscillation
public import PDEFoundation.Regularity.DyadicCampanato
public import PDEFoundation.Analysis.DyadicRadius

/-!
# Vector ball control implies coordinate cube Campanato control

This file converts a scale invariant centered `L²` estimate for a native
vector field on interior balls into the scalar dyadic cube estimate required
for each coordinate's Campanato representative.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The dimension-only loss from enclosing a cube in a Euclidean ball and
converting the ball radius back to the cube half-side. -/
def vectorBallCampanatoCoefficient (d : ℕ) : ℝ :=
  Real.sqrt ((Real.sqrt d) ^ d *
    (volume (euclideanBall (0 : Vec d) 1)).toReal) *
    (2 * Real.sqrt d)

/-- The cube half-side whose standard enclosing ball has radius `r₀`. -/
def vectorBallCampanatoBaseRadius (d : ℕ) (r₀ : ℝ) : ℝ :=
  r₀ / (2 * Real.sqrt d)

theorem vectorBallCampanatoBaseRadius_pos
    (hd : 0 < d) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    0 < vectorBallCampanatoBaseRadius d r₀ := by
  have hroot : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  unfold vectorBallCampanatoBaseRadius
  positivity

private theorem centeredAxisCube_vectorBallBase_subset_unit
    (hd : 0 < d) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    {z : Vec d} (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) :
    centeredAxisCube z (vectorBallCampanatoBaseRadius d r₀) ⊆
      euclideanBall (0 : Vec d) 1 := by
  have hroot : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hR : 0 < vectorBallCampanatoBaseRadius d r₀ :=
    vectorBallCampanatoBaseRadius_pos hd hr₀
  have hballRadius :
      2 * Real.sqrt d * vectorBallCampanatoBaseRadius d r₀ = r₀ := by
    unfold vectorBallCampanatoBaseRadius
    field_simp
  have hcube := centeredAxisCube_subset_euclideanBall hd z hR
  rw [hballRadius] at hcube
  have hsmall : euclideanBall z r₀ ⊆ euclideanBall z (1 / 2) :=
    euclideanBall_mono hr₀.le (hr₀le.trans (by norm_num))
  exact hcube.trans
    (hsmall.trans (euclideanBall_half_subset_unit_of_center_mem_half hz))

/-- A coordinate of a vector `L²` field is integrable on every base cube
centered in the half unit ball. -/
theorem integrableOn_coordinate_centeredAxisCube_vectorBallBase
    (hd : 0 < d) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) 1) g)
    {z : Vec d} (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) (i : Fin d) :
    IntegrableOn (fun x => g x i)
      (centeredAxisCube z (vectorBallCampanatoBaseRadius d r₀)) := by
  let Q := centeredAxisCube z (vectorBallCampanatoBaseRadius d r₀)
  have hQU : Q ⊆ euclideanBall (0 : Vec d) 1 := by
    simpa only [Q] using
      centeredAxisCube_vectorBallBase_subset_unit hd hr₀ hr₀le hz
  have hgi : MemL2On Q (fun x => g x i) :=
    (hg i).mono_measure (Measure.restrict_mono hQU le_rfl)
  let : IsFiniteMeasure (volumeOn Q) :=
    isFiniteMeasure_restrict.mpr
      (volume_centeredAxisCube_ne_top z
        (vectorBallCampanatoBaseRadius d r₀))
  exact hgi.integrable (by norm_num)

/-- The square of a coordinate is integrable on every base cube centered in
the half unit ball. -/
theorem integrableOn_sq_coordinate_centeredAxisCube_vectorBallBase
    (hd : 0 < d) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) 1) g)
    {z : Vec d} (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) (i : Fin d) :
    IntegrableOn (fun x => (g x i) ^ 2)
      (centeredAxisCube z (vectorBallCampanatoBaseRadius d r₀)) := by
  let Q := centeredAxisCube z (vectorBallCampanatoBaseRadius d r₀)
  have hQU : Q ⊆ euclideanBall (0 : Vec d) 1 := by
    simpa only [Q] using
      centeredAxisCube_vectorBallBase_subset_unit hd hr₀ hr₀le hz
  have hgi : MemL2On Q (fun x => g x i) :=
    (hg i).mono_measure (Measure.restrict_mono hQU le_rfl)
  simpa only [pow_two] using! hgi.integrable_mul hgi

/-- Interior centered vector mean bounds on balls give a dyadic scalar
Campanato row for every coordinate. -/
theorem dyadicCenteredCubeCampanatoBoundOn_coordinate_of_vectorBallScale
    (hd : 0 < d) {r₀ α K : ℝ} (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 4)
    (_hα0 : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    {g : Vec d → Vec d}
    (hg : MemVectorL2On (euclideanBall (0 : Vec d) 1) g)
    (hscale : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
        centeredVectorMeanL2 (euclideanBall z r) g ≤ K * r ^ α)
    (i : Fin d) :
    DyadicCenteredCubeCampanatoBoundOn (fun x => g x i)
      (euclideanBall (0 : Vec d) (1 / 2))
      (vectorBallCampanatoBaseRadius d r₀) α
      (vectorBallCampanatoCoefficient d * K) := by
  have hroot : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hdge1 : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)
  have hrootge1 : 1 ≤ Real.sqrt d := by
    simpa using Real.sqrt_le_sqrt hdge1
  have hfactor : 1 ≤ 2 * Real.sqrt d := by nlinarith
  have hfactorPower : (2 * Real.sqrt d) ^ α ≤ 2 * Real.sqrt d := by
    calc
      (2 * Real.sqrt d) ^ α ≤ (2 * Real.sqrt d) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hfactor hα1.le
      _ = 2 * Real.sqrt d := Real.rpow_one _
  have hR : 0 < vectorBallCampanatoBaseRadius d r₀ :=
    vectorBallCampanatoBaseRadius_pos hd hr₀
  intro z hz n
  let r := dyadicRadius (vectorBallCampanatoBaseRadius d r₀) n
  let rb := 2 * Real.sqrt d * r
  have hr : 0 < r := dyadicRadius_pos hR n
  have hrle : r ≤ vectorBallCampanatoBaseRadius d r₀ :=
    dyadicRadius_le hR.le n
  have hrb : 0 < rb := by dsimp [rb]; positivity
  have hrb_le : rb ≤ r₀ := by
    dsimp [rb]
    calc
      2 * Real.sqrt d * r ≤
          2 * Real.sqrt d * vectorBallCampanatoBaseRadius d r₀ :=
        mul_le_mul_of_nonneg_left hrle (by positivity)
      _ = r₀ := by
        unfold vectorBallCampanatoBaseRadius
        field_simp
  have hball : euclideanBall z rb ⊆ euclideanBall (0 : Vec d) 1 := by
    have hsmall : euclideanBall z rb ⊆ euclideanBall z (1 / 2) :=
      euclideanBall_mono hrb.le
        (hrb_le.trans (hr₀le.trans (by norm_num)))
    exact hsmall.trans (euclideanBall_half_subset_unit_of_center_mem_half hz)
  have hgBall : MemVectorL2On (euclideanBall z rb) g := fun j =>
    (hg j).mono_measure (Measure.restrict_mono hball le_rfl)
  have hcoord :=
    centeredCubeL2Oscillation_coordinate_le_enclosingBall_vectorMeanL2
      hd z hr hgBall i
  have hscale' := hscale z hz rb hrb hrb_le
  have hpow : rb ^ α = (2 * Real.sqrt d) ^ α * r ^ α := by
    dsimp [rb]
    exact Real.mul_rpow (by positivity) hr.le
  change centeredCubeL2Oscillation (fun x => g x i) z r ≤
    (vectorBallCampanatoCoefficient d * K) * r ^ α
  calc
    centeredCubeL2Oscillation (fun x => g x i) z r ≤
        Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) *
          centeredVectorMeanL2 (euclideanBall z rb) g := by
      simpa only [rb] using hcoord
    _ ≤ Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) *
          (K * rb ^ α) :=
      mul_le_mul_of_nonneg_left hscale' (Real.sqrt_nonneg _)
    _ = (Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) * K) *
          ((2 * Real.sqrt d) ^ α * r ^ α) := by rw [hpow]; ring
    _ ≤ (Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) * K) *
          ((2 * Real.sqrt d) * r ^ α) := by
      gcongr
    _ = (vectorBallCampanatoCoefficient d * K) * r ^ α := by
      unfold vectorBallCampanatoCoefficient
      ring

end

end PDE
