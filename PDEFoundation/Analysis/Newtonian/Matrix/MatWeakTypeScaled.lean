module

public import PDEFoundation.Analysis.Newtonian.Matrix.ScalingPotential
public import PDEFoundation.Analysis.Newtonian.Potential.Smooth

/-!
# Scaling the local weak-type estimate to a ball of radius `R`

If the local weak-type (1,1) estimate holds for fields supported in `B₁` (set in `B₂`) with
constant `C₀`, it holds with the same constant for fields supported in `B_R` (set in `B_{2R}`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem smul_mem_euclideanBall_iff {R : ℝ} (hR : 0 < R) (y : Vec d) (r : ℝ) :
    R • y ∈ euclideanBall (0 : Vec d) (R * r) ↔ y ∈ euclideanBall (0 : Vec d) r := by
  change euclideanSqDist (R • y) 0 < (R * r) ^ 2 ↔ euclideanSqDist y 0 < r ^ 2
  have h := euclideanSqDist_smul_smul R y 0
  rw [smul_zero] at h
  rw [h, mul_pow]
  exact mul_lt_mul_iff_right₀ (pow_pos hR 2)

theorem weakType_dilated {C₀ : ℝ} (hd : 0 < d)
    (hD3 : ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C₀ / lam * ∫ x, vecEuclideanNorm (F x)))
    {R : ℝ} (hR : 0 < R) {G : Vec d → Vec d}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (hGs : tsupport G ⊆ euclideanBall (0 : Vec d) R) {mu : ℝ} (hmu : 0 < mu) :
    volume {x | x ∈ euclideanBall (0 : Vec d) (2 * R) ∧
        mu < vecEuclideanNorm (classicalGradient (newtonPotential G) x)} ≤
      ENNReal.ofReal (C₀ / mu * ∫ x, vecEuclideanNorm (G x)) := by
  set G' : Vec d → Vec d := fun z => R • G (R • z) with hG'
  have hdetR : (R • (1 : Mat d)).det ≠ 0 := by
    rw [det_scalar]; exact pow_ne_zero _ hR.ne'
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun z : Vec d => R • z := contDiff_const_smul R
  have hG'c : ContDiff ℝ (⊤ : ℕ∞) G' := (contDiff_const_smul R).comp (hG.comp hφ)
  have hG'cs : HasCompactSupport G' := by
    have h := hasCompactSupport_matVecMul_comp (S := R • (1 : Mat d)) hdetR (B := R • (1 : Mat d)) hGc
    simpa only [matVecMul_scalar] using h
  have hG's : tsupport G' ⊆ euclideanBall (0 : Vec d) 1 := by
    have hsub : tsupport G' ⊆ (fun z : Vec d => R • z) ⁻¹' tsupport G := by
      refine tsupport_subset_preimage (continuous_const_smul R) (f := G) ?_
      intro z hz
      by_contra hz'
      apply hz
      have : G (R • z) = 0 := by simpa [Function.mem_support] using hz'
      simp [hG', this]
    intro z hz
    have h1 := hGs (hsub hz)
    have h2 : R • z ∈ euclideanBall (0 : Vec d) (R * 1) := by simpa using h1
    exact (smul_mem_euclideanBall_iff hR z 1).1 h2
  have hu : ContDiff ℝ (⊤ : ℕ∞) (newtonPotential G) := contDiff_newtonPotential hd hG hGc
  have hmain := hD3 G' hG'c hG's (R * mu) (mul_pos hR hmu)
  -- the set is the dilate of the set for `G'`
  set E' := {y | y ∈ euclideanBall (0 : Vec d) 2 ∧
      R * mu < vecEuclideanNorm (classicalGradient (newtonPotential G') y)} with hE'
  have hsub : {x | x ∈ euclideanBall (0 : Vec d) (2 * R) ∧
        mu < vecEuclideanNorm (classicalGradient (newtonPotential G) x)} ⊆
      (fun y => matVecMul (R • (1 : Mat d)) y) '' E' := by
    intro x hx
    refine ⟨R⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
    · have : R • (R⁻¹ • x) ∈ euclideanBall (0 : Vec d) (R * 2) := by
        rw [smul_inv_smul₀ hR.ne', mul_comm]; exact hx.1
      exact (smul_mem_euclideanBall_iff hR _ 2).1 this
    · rw [classicalGradient_newtonPotential_dilate hR _ hu, smul_inv_smul₀ hR.ne',
        vecEuclideanNorm_smul, abs_of_pos hR]
      exact mul_lt_mul_of_pos_left hx.2 hR
    · simp only [matVecMul_scalar, smul_inv_smul₀ hR.ne']
  have hint : ∫ x, vecEuclideanNorm (G' x) = R * ((R ^ d)⁻¹ * ∫ x, vecEuclideanNorm (G x)) := by
    have := integral_comp_matVecMul hdetR (fun v => vecEuclideanNorm (G v))
    simp only [matVecMul_scalar, det_scalar, abs_of_pos (pow_pos hR d)] at this
    rw [← this, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG', vecEuclideanNorm_smul, abs_of_pos hR]
  calc volume _ ≤ volume ((fun y => matVecMul (R • (1 : Mat d)) y) '' E') := measure_mono hsub
    _ = ENNReal.ofReal (R ^ d) * volume E' := by
        rw [volume_image_matVecMul, det_scalar, abs_of_pos (pow_pos hR d)]
    _ ≤ ENNReal.ofReal (R ^ d) * ENNReal.ofReal (C₀ / (R * mu) * ∫ x, vecEuclideanNorm (G' x)) := by
        gcongr
    _ = ENNReal.ofReal (C₀ / mu * ∫ x, vecEuclideanNorm (G x)) := by
        rw [← ENNReal.ofReal_mul (pow_pos hR d).le, hint]
        congr 1
        have : (R : ℝ) ≠ 0 := hR.ne'
        field_simp

end MatChange

end PDE
