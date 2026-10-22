module

public import EllipticRegularity.CalderonZygmund.QuadraticEllipsoid
public import PDEFoundation.Measure.CoefficientAverageQuadraticBounds
public import PDEFoundation.Measure.FiniteCoverMeanLp
public import PDEFoundation.Geometry.EuclideanBall.QuadraticEllipticVolume
public import PDEFoundation.Geometry.EuclideanBall.FiniteInteriorCover
/-! # Proof of `PDE.exists_calderonZygmund`

The actual average supplies only the quadratic bounds needed for normalization.
The cover and all norm-comparison constants are chosen before the exponent
and coefficients, so the forcing dependence stays linear in the exponent.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.CZGeneralProof

noncomputable section

open MeasureTheory

/-- Calderon--Zygmund estimate for coefficients close to their ball average. -/
theorem result
    (d : ℕ) (hd : 0 < d) (Lambda : ℝ) (hLambda : 1 ≤ Lambda) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsEllipticMatrix 1 Lambda (a x)) →
      (let A0 : Mat d := fun i j =>
          integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => a x i j)
        ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
          IsMatrixPerturbationLE (1 / (C * p)) (a x) A0) →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  classical
  let W := euclideanBall (0 : Vec d) 1
  let Q := euclideanBall (0 : Vec d) (1 / 2)
  let rho := 1 / (4 * Real.sqrt Lambda)
  have hSqrt : 1 ≤ Real.sqrt Lambda := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by simpa using hLambda)
  have hRho : 0 < rho := by dsimp only [rho]; positivity
  have hRhoQuarter : rho ≤ 1 / 4 := by
    dsimp only [rho]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [hSqrt]
  have hWPos : 0 < volume W := volume_euclideanBall_pos _ (by norm_num)
  have hWTop : volume W < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hQPos : 0 < volume Q := volume_euclideanBall_pos _ (by norm_num)
  have hQTop : volume Q < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  let m := volume (euclideanBall (0 : Vec d) rho)
  have hmPos : 0 < m := volume_euclideanBall_pos _ hRho
  have hmTop : m < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hRho.le)
  obtain ⟨H, hH, hLocal⟩ := exists_calderonZygmund_quadratic_ellipsoid_constants d hd
  obtain ⟨s, hsCenters, hsCover, _⟩ := exists_finset_euclideanBall_cover_closedHalf hRho hRhoQuarter
  obtain ⟨K, hK, hRestrict⟩ := exists_uniform_lpMeanNormOn_le_of_volume_lower
    (E := ℝ) W hWPos hWTop m hmPos hmTop
  obtain ⟨G, hG, hGlue⟩ := exists_uniform_eLpMeanNorm_le_of_finset_cover
    (E := ℝ) s Q (isOpen_euclideanBall _ _).measurableSet hQPos hQTop (volume W) hWTop
  let C : ℝ := max H (G * H * K * Real.sqrt Lambda)
  have hC : 1 ≤ C := hH.trans (le_max_left _ _)
  have hHC : H ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro p hp a ha hell hclose u F hFcoord hF hsol
  let A0 : Mat d := Matrix.of (fun i j => integralAverage W (fun x => a x i j))
  obtain ⟨_, hQuadratic⟩ := integrableOn_and_quadratic_bounds_symmPart_coefficientAverage
    (isOpen_euclideanBall _ _).measurableSet hWPos hWTop a hLambda ha hell
  have hLower : ∀ xi : Vec d, vecNormSq xi ≤ vecDot xi (matVecMul A0 xi) := by
    intro xi
    simpa only [A0, W, vecDot_symmPart_matVecMul] using (hQuadratic xi).1
  have hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lambda * vecNormSq xi :=
    fun xi => (hQuadratic xi).2
  have hCloseH : ∀ᵐ x ∂volumeOn W, IsMatrixPerturbationLE (1 / (H * p)) (a x) A0 := by
    filter_upwards [hclose] with x hx
    intro xi
    apply (hx xi).trans
    apply mul_le_mul_of_nonneg_right _ (vecEuclideanNorm_nonneg xi)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hHC (by linarith only [hp]))
  let e := quadraticEllipticNormalizerContinuousLinearEquiv hLower
  let E : Vec d → Set (Vec d) := fun z => e.symm '' euclideanBall (e z) rho
  let V : Vec d → Set (Vec d) := fun z => e.symm '' euclideanBall (e z) (rho / 2)
  have hGeom (z : Vec d) (hz : z ∈ s) :=
    quadraticEllipticNormalizer_quarter_volume_geometry hLambda hLower hUpper (hsCenters z hz)
  have hEUnit (z : Vec d) (hz : z ∈ s) : E z ⊆ W :=
    quadraticEllipticNormalizer_symm_image_quarter_subset_unitBall hLambda hLower hUpper (hsCenters z hz)
  have hVMeas (z : Vec d) (hz : z ∈ s) : MeasurableSet (V z) := (hGeom z hz).2.2.2.2.2.1
  have hVPos (z : Vec d) (hz : z ∈ s) : 0 < volume (V z) := (hGeom z hz).2.2.2.2.2.2.1
  have hVTop (z : Vec d) (hz : z ∈ s) : volume (V z) < ⊤ := (hGeom z hz).2.2.2.2.2.2.2.1
  have hVUpper (z : Vec d) (hz : z ∈ s) : volume (V z) ≤ volume W :=
    (hGeom z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCover : Q ⊆ ⋃ z ∈ s, V z := by
    intro x hx
    have hxCov := hsCover (euclideanBall_subset_euclideanClosedBall _ _ hx)
    simp only [Set.mem_iUnion] at hxCov ⊢
    obtain ⟨z, hz, hxz⟩ := hxCov
    exact ⟨z, hz, euclideanBall_half_quarter_subset_quadraticEllipticNormalizer_symm_image
      hLambda hLower z hxz⟩
  let U := Real.sqrt (integralAverage W (fun x => vecNormSq (u.grad x)))
  let NF := euclideanFieldLpMeanNormOn W (ENNReal.ofReal p) F
    (memLp_normalizedVolumeOn_of_memLpOn hF hWPos)
  let B := H * K * Real.sqrt Lambda * (U + p * NF)
  have hB : 0 ≤ B := by
    have hNF : 0 ≤ NF := ENNReal.toReal_nonneg
    have hU : 0 ≤ U := Real.sqrt_nonneg _
    dsimp only [B]
    positivity
  have hLocalBound : ∀ z ∈ s,
      ∃ _hg : MemLp (fun x => vecEuclideanNorm (u.grad x))
        (ENNReal.ofReal p) (volumeOn (V z)),
      (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        (normalizedVolumeOn (V z))).toReal ≤ B := by
    intro z hz
    obtain ⟨hEpos, hVpos, hFE, hg, hest⟩ := hLocal Lambda hLambda A0 hLower hUpper
      p hp a ha hCloseH u F hFcoord hF hsol z (hsCenters z hz)
    have hVolLow : m ≤ volume (E z) := (hGeom z hz).2.2.2.2.2.2.2.2.2.2.2.1
    have hForce := (hRestrict p hp (E z) (hEUnit z hz) hVolLow
      (fun x => vecEuclideanNorm (F x)) hF).2
    have hGradTwo : MemLp (fun x => vecEuclideanNorm (u.grad x))
        (ENNReal.ofReal (2 : ℝ)) (volumeOn W) := by
      simpa only [ENNReal.ofReal_ofNat] using u.gradMemL2.memLp_vecEuclideanNorm
    obtain ⟨hGradE, hEnergyMean⟩ := hRestrict 2 (by norm_num) (E z) (hEUnit z hz) hVolLow
      (fun x => vecEuclideanNorm (u.grad x)) hGradTwo
    have hEnergy : Real.sqrt (integralAverage (E z) (fun x => vecNormSq (u.grad x))) ≤ K * U := by
      rw [sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two
        (by simpa only [ENNReal.ofReal_ofNat] using memLp_normalizedVolumeOn_of_memLpOn hGradE hEpos),
        show U = euclideanFieldLpMeanNormOn W 2 u.grad
          (memLp_normalizedVolumeOn_of_memLpOn u.gradMemL2.memLp_vecEuclideanNorm hWPos) by
            exact sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two _]
      simpa only [ENNReal.ofReal_ofNat] using! hEnergyMean
    refine ⟨hg, hest.trans ?_⟩
    change H * (Real.sqrt Lambda * Real.sqrt (integralAverage (E z) (fun x => vecNormSq (u.grad x))) +
      p * (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (normalizedVolumeOn (E z))).toReal) ≤ B
    calc
      _ ≤ H * (Real.sqrt Lambda * (K * U) + p * (K * NF)) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hH)
        exact add_le_add (mul_le_mul_of_nonneg_left hEnergy (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left hForce (by linarith only [hp]))
      _ ≤ B := by
        dsimp only [B]
        have hU : 0 ≤ U := Real.sqrt_nonneg _
        have hNF : 0 ≤ NF := ENNReal.toReal_nonneg
        have hIncrease := mul_le_mul_of_nonneg_right hSqrt (mul_nonneg (by linarith only [hp]) hNF)
        have hScale := mul_le_mul_of_nonneg_left hIncrease (mul_nonneg (zero_le_one.trans hH) (zero_le_one.trans hK))
        nlinarith only [hScale]
  obtain ⟨hgrad, hest⟩ := hGlue p hp V hVMeas hCover hVPos hVTop hVUpper
    (fun x => vecEuclideanNorm (u.grad x)) B hB hLocalBound
  have hQW : Q ⊆ W := euclideanBall_mono (by norm_num) (by norm_num)
  let v := u.restrict (isOpen_euclideanBall _ _) hQW
  have hcoord : GradMemLpOn Q (ENNReal.ofReal p) v.grad := by
    intro i
    apply hgrad.of_le (v.gradMemL2 i).aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using!
      abs_apply_le_vecEuclideanNorm (u.grad x) i
  have hw := (v.toW1pOfGradMemLp hd (isOpenBoundedConvexDomain_euclideanBall _ (by norm_num))
    hQPos p hp hcoord).memW1p
  refine ⟨hw, hgrad, ?_⟩
  change (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
    (normalizedVolumeOn Q)).toReal ≤ C * (U + p * NF)
  apply hest.trans
  calc
    G * B = (G * H * K * Real.sqrt Lambda) * (U + p * NF) := by dsimp only [B]; ring
    _ ≤ C * (U + p * NF) := by
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      have hNF : 0 ≤ NF := ENNReal.toReal_nonneg
      have hU : 0 ≤ U := Real.sqrt_nonneg _
      positivity

end
end PDE.CZGeneralProof
