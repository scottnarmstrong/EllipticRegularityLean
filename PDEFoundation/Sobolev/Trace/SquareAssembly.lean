module

public import PDEFoundation.Sobolev.Trace.RawSlices
public import PDEFoundation.Sobolev.Trace.SquareSideLimits
public import PDEFoundation.Sobolev.Trace.Sides
public import PDEFoundation.Sobolev.Trace.SquareTraceProvenance

/-!
# Assembly of four square-side traces

This is the analytic assembly step below the `H¹` layer.  Its hypotheses are
the raw enlarged-side `L²` facts and the two dyadically summable error-energy
families supplied by a good-radius construction.  The primary conclusion
retains both concrete four-side trace data and its common smooth-sequence
provenance; no regularity assertion is stored as an opaque premise.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- A common smooth planar approximation with summable enlarged-square value
and Euclidean-gradient errors determines continuous weak traces on all four
sides of the selected square, while retaining exact equalities to the four
canonical limits of that common sequence. The Euclidean-gradient error is
kept exactly as `vecEuclideanNorm (classicalGradient (F n) x - g x)`; the
coordinate passage in the four side theorems has comparison constant one. -/
def squareTraceProvenanceOfGoodSmoothData
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r ρ : ℝ}
    (hr : 0 < r) (hρ : ρ ∈ Ioo r (2 * r))
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : HasRawEnlargedSquareSideSlices u x₀ r ρ)
    (hg : HasRawEnlargedSquareTangentialSlices g x₀ r ρ)
    (hValueSum : Summable (fun n => (2 : ℝ) ^ n *
      enlargedSquareSideScalarEnergy (fun x => F n x - u x) x₀ r ρ))
    (hGradientSum : Summable (fun n => (2 : ℝ) ^ n *
      enlargedSquareSideScalarEnergy
        (fun x => vecEuclideanNorm (classicalGradient (F n) x - g x))
        x₀ r ρ))
    (hValueRaw : ∀ n, HasRawEnlargedSquareSideSlices
      (fun x => F n x - u x) x₀ r ρ)
    (hGradientRaw : ∀ n, HasRawEnlargedSquareSideSlices
      (fun x => vecEuclideanNorm (classicalGradient (F n) x - g x))
        x₀ r ρ) :
    SquareTraceProvenance F u g x₀ ρ := by
  have hValueLimits :=
    tendsto_actual_square_side_scalar_error_integrals_of_summable hr hρ
      (fun n => by
        simpa only [IntegrableOn] using (hValueRaw n).1.integrable_sq)
      (fun n => by
        simpa only [IntegrableOn] using (hValueRaw n).2.1.integrable_sq)
      (fun n => by
        simpa only [IntegrableOn] using (hValueRaw n).2.2.1.integrable_sq)
      (fun n => by
        simpa only [IntegrableOn] using (hValueRaw n).2.2.2.integrable_sq)
      hValueSum
  have hGradientLimits :=
    tendsto_actual_square_side_scalar_error_integrals_of_summable hr hρ
      (fun n => by
        simpa only [IntegrableOn] using (hGradientRaw n).1.integrable_sq)
      (fun n => by
        simpa only [IntegrableOn] using (hGradientRaw n).2.1.integrable_sq)
      (fun n => by
        simpa only [IntegrableOn] using (hGradientRaw n).2.2.1.integrable_sq)
      (fun n => by
        simpa only [IntegrableOn] using (hGradientRaw n).2.2.2.integrable_sq)
      hGradientSum
  have hRight := squareLoopRightUniformLimit_of_tendsto_sq_vector_error
    hρ hF
    hu.1
    hg.1
    (fun n => by
      simpa only [squareLoopRightRestriction, squareLoopRightSide, Pi.sub_apply]
        using (hValueRaw n).1)
    (fun n => by
      simpa only [squareLoopRightSide] using (hGradientRaw n).1)
    (by
      simpa only [squareLoopRightRestriction, squareLoopRightSide,
        Pi.sub_apply, sq_abs] using hValueLimits.1)
    (by simpa only [squareLoopRightSide] using hGradientLimits.1)
  have hLeft := squareLoopLeftUniformLimit_of_tendsto_sq_vector_error
    hρ hF
    hu.2.1
    hg.2.1
    (fun n => by
      simpa only [squareLoopLeftRestriction, squareLoopLeftSide, Pi.sub_apply]
        using (hValueRaw n).2.1)
    (fun n => by
      simpa only [squareLoopLeftSide] using (hGradientRaw n).2.1)
    (by
      simpa only [squareLoopLeftRestriction, squareLoopLeftSide,
        Pi.sub_apply, sq_abs] using hValueLimits.2.1)
    (by simpa only [squareLoopLeftSide] using hGradientLimits.2.1)
  have hTop := squareLoopTopUniformLimit_of_tendsto_sq_vector_error
    hρ hF
    hu.2.2.1
    hg.2.2.1
    (fun n => by
      simpa only [squareLoopTopRestriction, squareLoopTopSide, Pi.sub_apply]
        using (hValueRaw n).2.2.1)
    (fun n => by
      simpa only [squareLoopTopSide] using (hGradientRaw n).2.2.1)
    (by
      simpa only [squareLoopTopRestriction, squareLoopTopSide,
        Pi.sub_apply, sq_abs] using hValueLimits.2.2.1)
    (by simpa only [squareLoopTopSide] using hGradientLimits.2.2.1)
  have hBottom := squareLoopBottomUniformLimit_of_tendsto_sq_vector_error
    hρ hF
    hu.2.2.2
    hg.2.2.2
    (fun n => by
      simpa only [squareLoopBottomRestriction, squareLoopBottomSide, Pi.sub_apply]
        using (hValueRaw n).2.2.2)
    (fun n => by
      simpa only [squareLoopBottomSide] using (hGradientRaw n).2.2.2)
    (by
      simpa only [squareLoopBottomRestriction, squareLoopBottomSide,
        Pi.sub_apply, sq_abs] using hValueLimits.2.2.2)
    (by simpa only [squareLoopBottomSide] using hGradientLimits.2.2.2)
  have hVerticalActual :
      Icc (x₀ 1 - ρ) (x₀ 1 + ρ) ⊆
        Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hHorizontalActual :
      Icc (x₀ 0 - ρ) (x₀ 0 + ρ) ⊆
        Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hRightRawMemL2 :
      MemLp (squareLoopRightRestriction u x₀ ρ) 2
        (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) :=
    hu.1.mono_measure
      (Measure.restrict_mono hVerticalActual le_rfl)
  have hLeftRawMemL2 :
      MemLp (squareLoopLeftRestriction u x₀ ρ) 2
        (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) :=
    hu.2.1.mono_measure
      (Measure.restrict_mono hVerticalActual le_rfl)
  have hTopRawMemL2 :
      MemLp (squareLoopTopRestriction u x₀ ρ) 2
        (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hu.2.2.1.mono_measure
      (Measure.restrict_mono hHorizontalActual le_rfl)
  have hBottomRawMemL2 :
      MemLp (squareLoopBottomRestriction u x₀ ρ) 2
        (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hu.2.2.2.mono_measure
      (Measure.restrict_mono hHorizontalActual le_rfl)
  have hRightTangentialMemL2 :
      MemLp (squareLoopRightTangentialRestriction g x₀ ρ) 2
        (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) :=
    hg.1.mono_measure
      (Measure.restrict_mono hVerticalActual le_rfl)
  have hLeftTangentialMemL2 :
      MemLp (squareLoopLeftTangentialRestriction g x₀ ρ) 2
        (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) :=
    hg.2.1.mono_measure
      (Measure.restrict_mono hVerticalActual le_rfl)
  have hTopTangentialMemL2 :
      MemLp (squareLoopTopTangentialRestriction g x₀ ρ) 2
        (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hg.2.2.1.mono_measure
      (Measure.restrict_mono hHorizontalActual le_rfl)
  have hBottomTangentialMemL2 :
      MemLp (squareLoopBottomTangentialRestriction g x₀ ρ) 2
        (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hg.2.2.2.mono_measure
      (Measure.restrict_mono hHorizontalActual le_rfl)
  rcases hRight with ⟨_, hRightContinuous, hRightAe, hRightWeak⟩
  rcases hLeft with ⟨_, hLeftContinuous, hLeftAe, hLeftWeak⟩
  rcases hTop with ⟨_, hTopContinuous, hTopAe, hTopWeak⟩
  rcases hBottom with ⟨_, hBottomContinuous, hBottomAe, hBottomWeak⟩
  have hRightMemL2 :
      MemLp (squareLoopRightUniformLimit F x₀ ρ) 2
        (volume.restrict (Ioo (x₀ 1 - ρ) (x₀ 1 + ρ))) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact MemLp.ae_eq hRightAe.symm hRightRawMemL2
  have hLeftMemL2 :
      MemLp (squareLoopLeftUniformLimit F x₀ ρ) 2
        (volume.restrict (Ioo (x₀ 1 - ρ) (x₀ 1 + ρ))) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact MemLp.ae_eq hLeftAe.symm hLeftRawMemL2
  have hTopMemL2 :
      MemLp (squareLoopTopUniformLimit F x₀ ρ) 2
        (volume.restrict (Ioo (x₀ 0 - ρ) (x₀ 0 + ρ))) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact MemLp.ae_eq hTopAe.symm hTopRawMemL2
  have hBottomMemL2 :
      MemLp (squareLoopBottomUniformLimit F x₀ ρ) 2
        (volume.restrict (Ioo (x₀ 0 - ρ) (x₀ 0 + ρ))) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact MemLp.ae_eq hBottomAe.symm hBottomRawMemL2
  refine {
    trace := {
      right := squareLoopRightUniformLimit F x₀ ρ
      left := squareLoopLeftUniformLimit F x₀ ρ
      top := squareLoopTopUniformLimit F x₀ ρ
      bottom := squareLoopBottomUniformLimit F x₀ ρ
      rightContinuous := hRightContinuous
      leftContinuous := hLeftContinuous
      topContinuous := hTopContinuous
      bottomContinuous := hBottomContinuous
      rightMemL2 := hRightMemL2
      leftMemL2 := hLeftMemL2
      topMemL2 := hTopMemL2
      bottomMemL2 := hBottomMemL2
      rightAeEq := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hRightAe
      leftAeEq := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hLeftAe
      topAeEq := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hTopAe
      bottomAeEq := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hBottomAe
      rightWeakDeriv := hRightWeak
      leftWeakDeriv := hLeftWeak
      topWeakDeriv := hTopWeak
      bottomWeakDeriv := hBottomWeak
      rightTangentialMemL2 := hRightTangentialMemL2
      leftTangentialMemL2 := hLeftTangentialMemL2
      topTangentialMemL2 := hTopTangentialMemL2
      bottomTangentialMemL2 := hBottomTangentialMemL2
      rightTop := squareLoopRightUniformLimit_eq_top_at_corner F x₀ ρ
      topLeft := squareLoopTopUniformLimit_eq_left_at_corner F x₀ ρ
      leftBottom := squareLoopLeftUniformLimit_eq_bottom_at_corner F x₀ ρ
      bottomRight := squareLoopBottomUniformLimit_eq_right_at_corner F x₀ ρ }
    right_eq := rfl
    left_eq := rfl
    top_eq := rfl
    bottom_eq := rfl }

/-- The trace-only view of
`squareTraceProvenanceOfGoodSmoothData`. This preserves the original API for
clients that do not yet need common-sequence endpoint provenance. -/
def squareSideTraceOfGoodSmoothData
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r ρ : ℝ}
    (hr : 0 < r) (hρ : ρ ∈ Ioo r (2 * r))
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : HasRawEnlargedSquareSideSlices u x₀ r ρ)
    (hg : HasRawEnlargedSquareTangentialSlices g x₀ r ρ)
    (hValueSum : Summable (fun n => (2 : ℝ) ^ n *
      enlargedSquareSideScalarEnergy (fun x => F n x - u x) x₀ r ρ))
    (hGradientSum : Summable (fun n => (2 : ℝ) ^ n *
      enlargedSquareSideScalarEnergy
        (fun x => vecEuclideanNorm (classicalGradient (F n) x - g x))
        x₀ r ρ))
    (hValueRaw : ∀ n, HasRawEnlargedSquareSideSlices
      (fun x => F n x - u x) x₀ r ρ)
    (hGradientRaw : ∀ n, HasRawEnlargedSquareSideSlices
      (fun x => vecEuclideanNorm (classicalGradient (F n) x - g x))
        x₀ r ρ) :
    SquareSideTrace u g x₀ ρ :=
  (squareTraceProvenanceOfGoodSmoothData hr hρ hF hu hg hValueSum hGradientSum
    hValueRaw hGradientRaw).trace

end

end PDE
