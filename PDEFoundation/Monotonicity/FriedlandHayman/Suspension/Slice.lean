module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.RadialTgn
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Lift
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Beta

/-!
# Friedland--Hayman: sphere integrals of radial lifts

The projection formula for continuous functions, and the sphere integrals over `∂B_r` of
`Φ²` and `|∇Φ|² - (y·∇Φ)²` for a radial lift `Φ = g(|y|) f(y/|y|)`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem vecEuclideanNorm_hilbert_smul {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (ω : Metric.sphere (0 : HilbertVec n) 1) :
    vecEuclideanNorm ((0 : Vec n) + r • (ω : HilbertVec n).toVec) = r := by
  have h1 : vecEuclideanNorm (ω : HilbertVec n).toVec = 1 := by
    unfold vecEuclideanNorm; rw [vecNormSq_toVec_sphere ω]; exact Real.sqrt_one
  rw [zero_add, vecEuclideanNorm_smul, abs_of_nonneg hr, h1, mul_one]

/-- The projection formula for continuous functions on the unit ball. -/
theorem sphereIntegral_comp_projFst_cont {n N : ℕ} [NeZero n] [NeZero N] {G : Vec n → ℝ}
    (hG : Continuous G) :
    sphereIntegral (0 : Vec (n + N)) 1 (fun x => G (projFst x)) =
      sphereArea N * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.sin θ ^ (N - 1) * sphereIntegral (0 : Vec n) (Real.cos θ) G := by
  set Kc : Set (Vec n) := {y | vecEuclideanNorm y ≤ 1} with hKc
  have hKcc : IsClosed Kc := isClosed_le continuous_vecEuclideanNorm continuous_const
  have hKcom : IsCompact Kc := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec n) 1) hKcc fun y hy => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    exact (abs_apply_le_vecEuclideanNorm y i).trans hy
  obtain ⟨C, hC⟩ := hKcom.exists_bound_of_continuousOn hG.continuousOn
  set G' : Vec n → ℝ := Kc.indicator G with hG'
  have hmeas : Measurable G' := hG.measurable.indicator hKcc.measurableSet
  have hb : ∀ y, |G' y| ≤ max C 0 := by
    intro y
    by_cases hy : y ∈ Kc
    · rw [hG', Set.indicator_of_mem hy, ← Real.norm_eq_abs]; exact (hC y hy).trans (le_max_left _ _)
    · rw [hG', Set.indicator_of_notMem hy, abs_zero]; exact le_max_right _ _
  have h1 : sphereIntegral (0 : Vec (n + N)) 1 (fun x => G (projFst x)) =
      sphereIntegral (0 : Vec (n + N)) 1 (fun x => G' (projFst x)) := by
    refine sphereIntegral_congr_sphere fun x hx => ?_
    rw [hG', Set.indicator_of_mem (show projFst x ∈ Kc from vecEuclideanNorm_projFst_le_one hx)]
  rw [h1, sphereIntegral_comp_projFst G' hmeas ⟨max C 0, hb⟩]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
  have hc0 : 0 ≤ Real.cos θ := cos_nonneg_of_mem hθ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  congr 1
  unfold sphereIntegral
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  beta_reduce
  rw [hG', Set.indicator_of_mem]
  rw [hKc, Set.mem_ofPred_eq, vecEuclideanNorm_hilbert_smul hc0 ω]
  exact hc1

theorem continuous_tgn {n : ℕ} {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (tangentialGradientNormSq f) := by
  have hg := PDE.ContDiff.continuous_classicalGradient hf
  unfold tangentialGradientNormSq vecNormSq vecDot
  refine Continuous.sub ?_ (Continuous.pow ?_ 2)
  · exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hg).mul
      ((continuous_apply i).comp hg)
  · exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hg).mul (continuous_apply i)

theorem sphereIntegral_unit {d : ℕ} (h : Vec d → ℝ) :
    sphereIntegral (0 : Vec d) 1 h =
      ∫ ω : Metric.sphere (0 : HilbertVec d) 1, h (ω : HilbertVec d).toVec
        ∂((volume : Measure (HilbertVec d)).toSphere) := by
  simp [sphereIntegral]

theorem integrable_sphere_of_continuous {d : ℕ} {h : Vec d → ℝ} (hh : Continuous h) :
    Integrable (fun ω : Metric.sphere (0 : HilbertVec d) 1 => h (ω : HilbertVec d).toVec)
      ((volume : Measure (HilbertVec d)).toSphere) :=
  (hh.comp (continuous_toVec.comp continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The tangential gradient quantity of a radial lift. -/
def radialGradQ {n : ℕ} (g : ℝ → ℝ) (f : Vec n → ℝ) (y : Vec n) : ℝ :=
  vecNormSq (classicalGradient (radialLift g f) y) -
    vecDot (classicalGradient (radialLift g f) y) y ^ 2

theorem sphereIntegral_radialLift_sq {n : ℕ} {g : ℝ → ℝ} {f : Vec n → ℝ} {r : ℝ} (hr : 0 < r) :
    sphereIntegral (0 : Vec n) r (fun y => radialLift g f y ^ 2) =
      r ^ (n - 1) * (g r ^ 2 * sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2)) := by
  rw [sphereIntegral_unit (fun x => f x ^ 2)]
  unfold sphereIntegral
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hn := vecEuclideanNorm_hilbert_smul hr.le ω
  beta_reduce
  unfold radialLift
  rw [hn, zero_add, inv_smul_smul₀ hr.ne']
  ring

theorem sphereIntegral_radialGradQ {n : ℕ} {g : ℝ → ℝ} {g' : ℝ} {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) {r : ℝ} (hr : 0 < r) (hg : HasDerivAt g g' r) :
    sphereIntegral (0 : Vec n) r (radialGradQ g f) =
      r ^ (n - 1) * ((1 - r ^ 2) * (g' ^ 2 * sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2)) +
        (g r / r) ^ 2 * sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f)) := by
  have hI := integrable_sphere_of_continuous (d := n) (h := fun x => f x ^ 2)
    (hf.continuous.pow 2)
  have hJ := integrable_sphere_of_continuous (d := n) (h := tangentialGradientNormSq f)
    (continuous_tgn hf)
  rw [sphereIntegral_unit (fun x => f x ^ 2), sphereIntegral_unit (tangentialGradientNormSq f)]
  unfold sphereIntegral
  congr 1
  have hsum : ∫ ω : Metric.sphere (0 : HilbertVec n) 1,
      ((1 - r ^ 2) * (g' ^ 2 * f (ω : HilbertVec n).toVec ^ 2) +
        (g r / r) ^ 2 * tangentialGradientNormSq f (ω : HilbertVec n).toVec)
        ∂((volume : Measure (HilbertVec n)).toSphere) =
      (1 - r ^ 2) * (g' ^ 2 * ∫ ω : Metric.sphere (0 : HilbertVec n) 1,
        f (ω : HilbertVec n).toVec ^ 2 ∂((volume : Measure (HilbertVec n)).toSphere)) +
      (g r / r) ^ 2 * ∫ ω : Metric.sphere (0 : HilbertVec n) 1,
        tangentialGradientNormSq f (ω : HilbertVec n).toVec
          ∂((volume : Measure (HilbertVec n)).toSphere) := by
    rw [integral_add ((hI.const_mul (g' ^ 2)).const_mul _) (hJ.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul]
  simp only [zero_add]
  rw [← hsum]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hn := vecEuclideanNorm_hilbert_smul hr.le ω
  rw [zero_add] at hn
  have hy : r • (ω : HilbertVec n).toVec ≠ 0 := by
    intro h0
    rw [h0] at hn
    have : vecEuclideanNorm (0 : Vec n) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    linarith
  have := tgn_radialLift hf hy (by rw [hn]; exact hg)
  rw [hn, inv_smul_smul₀ hr.ne'] at this
  exact this

end Susp

end

end PDE.FHLane
