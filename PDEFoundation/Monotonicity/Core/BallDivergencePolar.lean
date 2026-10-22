module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Analysis.HilbertPolar
public import PDEFoundation.Analysis.HilbertDictionary
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Polar coordinates for radial integrands on `Vec d`

For a continuous `g` and a continuous radial weight `c` vanishing for `t > r²`,
`∫ c(|x|²) g(x) dx = ∫_{s > 0} c(s²) · sphereIntegral 0 s g ds`, with
`PDE.sphereIntegral`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.BallDivergence

noncomputable section

theorem vecNormSq_toVec {d : ℕ} (z : HilbertVec d) : vecNormSq z.toVec = ‖z‖ ^ 2 := by
  rw [HilbertVec.norm_eq_vecEuclideanNorm, vecEuclideanNorm_sq]

theorem continuous_toVec {d : ℕ} : Continuous (fun z : HilbertVec d => z.toVec) :=
  (Internal.toHilbert (d := d)).symm.continuous

/-- Polar coordinates for a radial weight times a continuous function. -/
theorem integral_radial_mul_eq_integral_Ioi_sphereIntegral {d : ℕ} [NeZero d]
    {g : Vec d → ℝ} (hg : Continuous g) {c : ℝ → ℝ} (hc : Continuous c) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : ∀ t, r ^ 2 < t → c t = 0) :
    ∫ x, c (vecNormSq x) * g x =
      ∫ s in Ioi (0 : ℝ), c (s ^ 2) * sphereIntegral (0 : Vec d) s g := by
  let h : Vec d → ℝ := fun x => c (vecNormSq x) * g x
  let G : HilbertVec d → ℝ := fun z => h z.toVec
  have hcont : Continuous h := (hc.comp contDiff_vecNormSq.continuous).mul hg
  have hcs : HasCompactSupport h := by
    apply HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hr)
    intro x hx
    have hx' : r ^ 2 < euclideanSqDist x 0 := not_le.1 hx
    have : euclideanSqDist x 0 = vecNormSq x := by simp [euclideanSqDist]
    simp only [h, hsupp _ (this ▸ hx'), zero_mul]
  have hGeq : G = h ∘ (Internal.toHilbert (d := d)).symm := rfl
  have hGcont : Continuous G := by
    rw [hGeq]; exact hcont.comp (Internal.toHilbert (d := d)).symm.continuous
  have hGcs : HasCompactSupport G := by
    rw [hGeq]; exact hcs.comp_homeomorph (Internal.toHilbert (d := d)).symm.toHomeomorph
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGcs
  have htr : ∫ x, h x = ∫ z, G z := by
    rw [← Internal.measurePreserving_toHilbert.integral_comp
      (Internal.toHilbert (d := d)).toHomeomorph.measurableEmbedding G]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [G])
  have hpolar := Internal.integral_eq_integral_Ioi_sphere hGint
  show ∫ x, h x = _
  rw [htr, hpolar]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  have hfun : ∀ ω : Metric.sphere (0 : HilbertVec d) 1, G (s • (ω : HilbertVec d)) =
      c (s ^ 2) * g ((0 : Vec d) + s • (ω : HilbertVec d).toVec) := by
    intro ω
    have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have h1 : vecNormSq (s • (ω : HilbertVec d)).toVec = s ^ 2 := by
      rw [vecNormSq_toVec, norm_smul, hn, Real.norm_eq_abs, mul_one, sq_abs]
    have h2 : (s • (ω : HilbertVec d)).toVec = (0 : Vec d) + s • (ω : HilbertVec d).toVec := by
      ext i; simp [HilbertVec.toVec_apply]
    show c (vecNormSq (s • (ω : HilbertVec d)).toVec) * g (s • (ω : HilbertVec d)).toVec = _
    rw [h1, h2]
  simp only [hfun, integral_const_mul, sphereIntegral, Internal.sphereMeasure, smul_eq_mul]
  ring

end

end PDE.BallDivergence
