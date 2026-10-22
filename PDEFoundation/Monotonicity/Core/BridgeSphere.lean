module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Analysis.HilbertBallAverage
public import PDEFoundation.Analysis.HilbertDictionary
public import PDEFoundation.Analysis.HilbertPolar
public import PDEFoundation.Analysis.HilbertSphereAverage

/-!
# Chapter 2 bridge: spheres and polar form on `Vec d`

Transport of the `sphereMean`/`sphereIntegral` to the internal Hilbert sphere averages,
the polar form of ball integrals and the radial derivative of a ball integral, all stated on
`Vec d`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The total surface measure `σ_d` of the unit sphere. -/
def sphereArea (d : ℕ) : ℝ := (Internal.sphereMeasure d).real Set.univ

theorem sphereArea_pos [NeZero d] : 0 < sphereArea d := by
  have h := Internal.sphereMeasure_real_univ_ne_zero (d := d)
  exact lt_of_le_of_ne measureReal_nonneg (Ne.symm h)

theorem sphereArea_ne_zero [NeZero d] : sphereArea d ≠ 0 := sphereArea_pos.ne'

theorem sphereMean_eq_sphereAverage (x : Vec d) (r : ℝ) (f : Vec d → ℝ) :
    sphereMean x r f = Internal.sphereAverage x.toHilbertVec r (fun y => f y.toVec) := by
  unfold sphereMean Internal.sphereAverage Internal.sphereMeasure
  simp [Vec.toHilbertVec, HilbertVec.toVec]

theorem sphereIntegral_eq_mul_sphereMean [NeZero d] (x : Vec d) (r : ℝ) (f : Vec d → ℝ) :
    sphereIntegral x r f = sphereArea d * r ^ (d - 1) * sphereMean x r f := by
  unfold sphereIntegral sphereMean sphereArea
  rw [average_eq, smul_eq_mul]
  simp only [Measure.real]
  have h : (Internal.sphereMeasure d).real Set.univ ≠ 0 :=
    Internal.sphereMeasure_real_univ_ne_zero
  simp only [Internal.sphereMeasure, Measure.real] at h ⊢
  have : (((volume : Measure (HilbertVec d)).toSphere) Set.univ).toReal ≠ 0 := h
  field_simp


theorem continuous_toVec : Continuous (HilbertVec.toVec : HilbertVec d → Vec d) :=
  Internal.toHilbert.symm.continuous

theorem continuousAt_sphereMean [NeZero d] {g : Vec d → ℝ} (hg : Continuous g)
    (x : Vec d) (r₀ : ℝ) : ContinuousAt (fun r => sphereMean x r g) r₀ := by
  simp_rw [sphereMean_eq_sphereAverage]
  exact Internal.continuousAt_sphereAverage (hg.comp continuous_toVec) _ _

theorem continuous_sphereMean [NeZero d] {g : Vec d → ℝ} (hg : Continuous g) (x : Vec d) :
    Continuous (fun r => sphereMean x r g) :=
  continuous_iff_continuousAt.mpr (continuousAt_sphereMean hg x)

theorem continuous_sphereIntegral [NeZero d] {g : Vec d → ℝ} (hg : Continuous g) (x : Vec d) :
    Continuous (fun r => sphereIntegral x r g) := by
  simp_rw [sphereIntegral_eq_mul_sphereMean]
  exact (continuous_const.mul (continuous_pow _)).mul (continuous_sphereMean hg x)

theorem integral_euclideanBall_eq_hilbert (g : Vec d → ℝ) (x : Vec d) {r : ℝ} (hr : 0 < r) :
    ∫ y in euclideanBall x r, g y =
      ∫ z in Metric.ball x.toHilbertVec r, g z.toVec := by
  rw [← Internal.preimage_ball_toHilbert x hr]
  have := (Internal.measurePreserving_toHilbert (d := d)).setIntegral_preimage_emb
    (Internal.toHilbert.toHomeomorph.measurableEmbedding)
    (fun z : HilbertVec d => g z.toVec) (Metric.ball (Internal.toHilbert x) r)
  simpa using this

/-- Polar form of a ball integral in `Vec d` terms. -/
theorem integral_euclideanBall_eq_intervalIntegral_sphereIntegral [NeZero d]
    {g : Vec d → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r) :
    ∫ y in euclideanBall 0 r, g y = ∫ t in (0 : ℝ)..r, sphereIntegral 0 t g := by
  rw [integral_euclideanBall_eq_hilbert g 0 hr]
  have h0 : (0 : Vec d).toHilbertVec = 0 := by ext i; simp [Vec.toHilbertVec_apply]
  rw [h0, Internal.integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage
    (u := fun z : HilbertVec d => g z.toVec) (hg.comp continuous_toVec) 0 hr, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [sphereIntegral_eq_mul_sphereMean, sphereMean_eq_sphereAverage, h0]
  simp only [sphereArea]
  ring

theorem hasDerivAt_integral_euclideanBall [NeZero d] {g : Vec d → ℝ} (hg : Continuous g)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ∫ y in euclideanBall 0 s, g y) (sphereIntegral 0 r g) r := by
  have hc := continuous_sphereIntegral hg (0 : Vec d)
  have hD : HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, sphereIntegral 0 t g)
      (sphereIntegral 0 r g) r :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact integral_euclideanBall_eq_intervalIntegral_sphereIntegral hg hs

end

end PDE

