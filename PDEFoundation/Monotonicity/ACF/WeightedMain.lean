module

public import PDEFoundation.Monotonicity.ACF.WeightedAssembly
public import PDEFoundation.Monotonicity.Core.RellichSphere

/-!
# ACF-W: the weighted bound and finiteness

For `3 ≤ d`, `u ∈ H¹(B_R)` continuous, nonnegative and weakly subharmonic:

1. `acfWeightedEnergy u.grad r ≠ ⊤` for every `r ∈ (0, R)`;
2. for a.e. `r ∈ (0, R)` the slices of `u²`, `(∂_r u)²`, `|∇u|²` are integrable and
   `J(r) ≤ r^{2-d} (√(a b) + (d-2) a / (2 r))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {d : ℕ} {R : ℝ}

theorem vecEuclideanNorm_slice {r : ℝ} (hr : 0 < r) (ω : Metric.sphere (0 : HilbertVec d) 1) :
    vecEuclideanNorm ((0 : Vec d) + r • (ω : HilbertVec d).toVec) = r := by
  have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have e : ((0 : Vec d) + r • (ω : HilbertVec d).toVec) = r • (ω : HilbertVec d).toVec := by
    ext i; simp
  unfold vecEuclideanNorm
  rw [e, vecNormSq_smul, BallDivergence.vecNormSq_toVec, hn, one_pow, mul_one]
  exact Real.sqrt_sq hr.le

/-- Cauchy--Schwarz for the radial flux on the sphere. -/
theorem acfSliceFlux_le {u : Vec d → ℝ} {G : Vec d → Vec d} {r : ℝ} (hr : 0 < r)
    (hf2 : SphereIntegrable r (fun x => u x ^ 2))
    (hg2 : SphereIntegrable r (fun x => radialDeriv G x ^ 2))
    (hfg : SphereIntegrable r (fun x => u x * radialDeriv G x)) :
    acfSliceFlux u G r ≤ r * Real.sqrt (acfSliceMass u r * acfSliceRadial G r) := by
  set μ := (volume : Measure (HilbertVec d)).toSphere with hμ
  set f : Metric.sphere (0 : HilbertVec d) 1 → ℝ :=
    fun ω => u ((0 : Vec d) + r • (ω : HilbertVec d).toVec) with hf
  set g : Metric.sphere (0 : HilbertVec d) 1 → ℝ :=
    fun ω => radialDeriv G ((0 : Vec d) + r • (ω : HilbertVec d).toVec) with hg
  have hcs := integral_mul_sq_le (μ := μ) (f := f) (g := g) hf2 hg2 hfg
  have hflux : acfSliceFlux u G r = r * (r ^ (d - 1) * ∫ ω, f ω * g ω ∂μ) := by
    unfold acfSliceFlux sphereIntegral
    have : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
        u ((0 : Vec d) + r • (ω : HilbertVec d).toVec) *
          vecDot ((0 : Vec d) + r • (ω : HilbertVec d).toVec)
            (G ((0 : Vec d) + r • (ω : HilbertVec d).toVec)) = r * (f ω * g ω) := by
      intro ω
      have hnorm := vecEuclideanNorm_slice hr ω
      have hdot : vecDot ((0 : Vec d) + r • (ω : HilbertVec d).toVec)
          (G ((0 : Vec d) + r • (ω : HilbertVec d).toVec)) = r * g ω := by
        simp only [hg, radialDeriv, hnorm]
        field_simp
      rw [hdot]; simp only [hf]; ring
    simp only [this]
    rw [integral_const_mul]
    ring
  have ha : acfSliceMass u r = r ^ (d - 1) * ∫ ω, f ω ^ 2 ∂μ := rfl
  have hb : acfSliceRadial G r = r ^ (d - 1) * ∫ ω, g ω ^ 2 ∂μ := rfl
  rw [hflux]
  refine mul_le_mul_of_nonneg_left ?_ hr.le
  have hsq : (r ^ (d - 1) * ∫ ω, f ω * g ω ∂μ) ^ 2 ≤ acfSliceMass u r * acfSliceRadial G r := by
    rw [ha, hb, mul_pow]
    calc (r ^ (d - 1)) ^ 2 * (∫ ω, f ω * g ω ∂μ) ^ 2
        ≤ (r ^ (d - 1)) ^ 2 * ((∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = _ := by ring
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-- **ACF-W, item 1: finiteness.** -/
theorem acfWeightedEnergy_ne_top (hd : 3 ≤ d) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) R) :
    acfWeightedEnergy u.grad r ≠ ⊤ := by
  have hk : 0 < (R - r) / 2 := by linarith [hr.2]
  have hrk : r + (R - r) / 2 < R := by linarith [hr.2]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (acf_energy_le_kernel hd hr.1 hk hrk u hcont hnonneg hsub)

/-- **ACF-W, item 2: the weighted bound for a.e. `r`.**  With
`a = ∫_{∂B_r} u²`, `b = ∫_{∂B_r} (∂_r u)²` (`acfSliceMass`, `acfSliceRadial`), for a.e.
`r ∈ (0, R)` the slices of `u²`, `(∂_r u)²` and `|∇u|²` are integrable and
`J(r) ≤ r^{2-d} (√(a b) + (d-2) a / (2 r))`. -/
theorem acf_weighted_bound_ae (hd : 3 ≤ d) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SphereIntegrable r (fun x => u.toFun x ^ 2) ∧
      SphereIntegrable r (fun x => radialDeriv u.grad x ^ 2) ∧
      SphereIntegrable r (fun x => vecNormSq (u.grad x)) ∧
      acfWeightedEnergy u.grad r ≤ ENNReal.ofReal ((r ^ (d - 2))⁻¹ *
        (Real.sqrt (acfSliceMass u.toFun r * acfSliceRadial u.grad r) +
          ((d : ℝ) - 2) * acfSliceMass u.toFun r / (2 * r))) := by
  have : NeZero d := ⟨by omega⟩
  filter_upwards [ae_energy_le_profile hd u hcont hnonneg hsub,
    ae_sphereIntegrable_of_integrableOn (integrableOn_sq_u u),
    ae_sphereIntegrable_of_integrableOn (integrableOn_sq_radialDeriv u),
    ae_sphereIntegrable_of_integrableOn (integrableOn_mul_radialDeriv u),
    ae_sphereIntegrable_of_integrableOn (integrableOn_vecNormSq_grad u),
    ae_restrict_mem measurableSet_Ioo] with r h1 h2 h3 h4 h5 hrm
  refine ⟨h2, h3, h5, h1.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hr0 : 0 < r := hrm.1
  have hF := acfSliceFlux_le hr0 h2 h3 h4
  have hpow : r ^ (d - 1) = r ^ (d - 2) * r := by
    rw [← pow_succ]; congr 1; omega
  have hpos : 0 < r ^ (d - 2) * r := by positivity
  unfold acfProfile
  calc (acfSliceFlux u.toFun u.grad r + (((d : ℝ) - 2) / 2) * acfSliceMass u.toFun r) /
        r ^ (d - 1)
      ≤ (r * Real.sqrt (acfSliceMass u.toFun r * acfSliceRadial u.grad r) +
          (((d : ℝ) - 2) / 2) * acfSliceMass u.toFun r) / r ^ (d - 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
    _ = (r ^ (d - 2))⁻¹ * (Real.sqrt (acfSliceMass u.toFun r * acfSliceRadial u.grad r) +
          ((d : ℝ) - 2) * acfSliceMass u.toFun r / (2 * r)) := by
        rw [hpow]
        have : r ^ (d - 2) ≠ 0 := by positivity
        field_simp

end

end PDE
