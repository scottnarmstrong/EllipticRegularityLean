module

public import CZStatements.Identity
public import PDEFoundation.PDE.AffineChange
public import PDEFoundation.Measure.AffineNormalizedVolume
public import PDEFoundation.Sobolev.H1.GradientLpUpgrade

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped _root_.ENNReal Pointwise
noncomputable section

/-- The identity-coefficient Calderón–Zygmund estimate on an arbitrary round ball.
The constant is chosen before the exponent, center, radius, coefficients, and data.
The amplitude-normalized affine change preserves the exact normalized estimate. -/
theorem exists_calderonZygmund_identity_ball_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (R : ℝ) (hR : 0 < R), ∀ (z : Vec d) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall z R))) →
      (∀ᵐ x ∂volumeOn (euclideanBall z R),
        IsMatrixPerturbationLE (1 / (C * p)) (a x) (1 : Mat d)) →
      ∀ (u : H1Function (euclideanBall z R))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall z R))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall z R))),
      IsWeakDivergenceFormSolutionOn a
          (euclideanBall z R) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall z (R / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall z (R / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall z (R / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos z (by positivity))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall z R)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall z R) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos z hR))) := by
  obtain ⟨C, hC, hIdentity⟩ := exists_calderonZygmund_identity d hd
  refine ⟨C, hC, ?_⟩
  intro p hp R hR z a ha hclose u F hFcoord hF hsol
  let BR := euclideanBall (0 : Vec d) R
  have htranslate : translateSet (-z) (euclideanBall z R) = BR := by
    ext x
    rw [mem_translateSet_iff_sub_mem]
    simp only [sub_neg_eq_add]
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR,
      mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simp [sub_eq_add_neg, add_assoc]
  let uraw := u.translate (-z)
  let uR : H1Function BR := uraw.restrict (isOpen_euclideanBall _ _)
    (htranslate ▸ Set.Subset.rfl)
  let aR : CoeffField d := fun x => a (x + z)
  let FR : Vec d → Vec d := fun x => F (x + z)
  have hsolraw := hsol.translate (-z)
  have hopenraw : IsOpen (translateSet (-z) (euclideanBall z R)) := by
    rw [htranslate]
    exact isOpen_euclideanBall _ _
  have hsolR : IsWeakDivergenceFormSolutionOn aR BR uR 0 FR := by
    simpa only [aR, FR, uR, uraw, sub_neg_eq_add] using!
      hsolraw.restrict hopenraw (isOpen_euclideanBall _ _) (htranslate ▸ Set.Subset.rfl)
  have hscale : R⁻¹ • BR = euclideanBall (0 : Vec d) 1 := by
    dsimp only [BR]
    rw [euclideanBall_eq_translateSet_smul_unit_of_pos (0 : Vec d) hR]
    simp only [translateSet_zero, smul_smul]
    rw [inv_mul_cancel₀ hR.ne', one_smul]
  let usraw := uR.dilate (inv_pos.mpr hR)
  have hunitSub : euclideanBall (0 : Vec d) 1 ⊆ R⁻¹ • BR := by
    rw [hscale]
  let u0 : H1Function (euclideanBall (0 : Vec d) 1) :=
    usraw.restrict (isOpen_euclideanBall _ _) hunitSub
  let a0 : CoeffField d := fun x => aR (R • x)
  let F0 : Vec d → Vec d := fun x => FR (R • x)
  have hsolsraw := hsolR.dilate_of_pos (inv_pos.mpr hR)
  have hopensraw : IsOpen (R⁻¹ • BR) := by
    rw [hscale]
    exact isOpen_euclideanBall _ _
  have hsol0 : IsWeakDivergenceFormSolutionOn a0
      (euclideanBall (0 : Vec d) 1) u0 0 F0 := by
    have hs := hsolsraw.restrict hopensraw (isOpen_euclideanBall _ _)
      hunitSub
    simpa only [a0, F0, u0, usraw, inv_inv, Pi.zero_apply, mul_zero,
      inv_mul_cancel₀ hR.ne', one_mul, smul_eq_mul] using! hs
  let B := euclideanBall z R
  let U := euclideanBall (0 : Vec d) 1
  have hBpos : 0 < volume B := volume_euclideanBall_pos _ hR
  have hBtop : volume B < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hR.le)
  have hUpos : 0 < volume U := volume_euclideanBall_pos _ (by norm_num)
  have hUtop : volume U < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hForward := measurePreserving_smul_addRight_normalizedVolumeOn_euclideanBall hR z
  have ha0 : ∀ i j, AEMeasurable (fun x => a0 x i j) (volumeOn U) := by
    intro i j
    have hn := ((ha i j).smul_measure ((volume B)⁻¹)).comp_quasiMeasurePreserving
      hForward.quasiMeasurePreserving
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hUpos hUtop]
    simpa only [a0, aR, Function.comp_apply] using! hn.smul_measure (volume U)
  have hclose0 : ∀ᵐ x ∂volumeOn U, IsMatrixPerturbationLE (1 / (C * p)) (a0 x) 1 := by
    have hn := hForward.quasiMeasurePreserving.ae (Measure.ae_smul_measure hclose ((volume B)⁻¹))
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hUpos hUtop]
    simpa only [a0, aR] using Measure.ae_smul_measure hn (volume U)
  have hFcoord0 : ∀ i, AEStronglyMeasurable (fun x => F0 x i) (volumeOn U) := by
    intro i
    have hn := ((hFcoord i).smul_measure ((volume B)⁻¹)).comp_quasiMeasurePreserving
      hForward.quasiMeasurePreserving
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hUpos hUtop]
    simpa only [F0, FR, Function.comp_apply] using! hn.smul_measure (volume U)
  have hFMean := memLp_normalizedVolumeOn_of_memLpOn hF hBpos
  have hF0Mean : MemLp (fun x => vecEuclideanNorm (F0 x)) (ENNReal.ofReal p)
      (normalizedVolumeOn U) := by
    simpa only [F0, FR, Function.comp_apply] using! hFMean.comp_measurePreserving hForward
  have hF0 : MemLp (fun x => vecEuclideanNorm (F0 x)) (ENNReal.ofReal p) (volumeOn U) := by
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hUpos hUtop]
    exact hF0Mean.smul_measure hUtop.ne
  obtain ⟨_, hgrad0, hest0⟩ := hIdentity p hp a0 ha0 hclose0 u0 F0 hFcoord0 hF0 hsol0
  have hGrad0Eq : u0.grad = fun x => u.grad (R • x + z) := by
    funext x
    simp only [u0, usraw, uR, uraw, H1Function.restrict_grad,
      H1Function.dilate_grad, H1Function.translate_grad]
    congr 1
    ext i
    simp
  let BH := euclideanBall (0 : Vec d) (1 / 2)
  let V := euclideanBall z (R / 2)
  have hVpos : 0 < volume V := volume_euclideanBall_pos _ (by positivity)
  have hVtop : volume V < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by positivity))
  have hBHpos : 0 < volume BH := volume_euclideanBall_pos _ (by norm_num)
  have hHalfSet : translateSet z (R • BH) = V := by
    dsimp only [V]
    rw [euclideanBall_eq_translateSet_smul_unit_of_pos z (div_pos hR (by norm_num))]
    congr 1
    have hBH : BH = (1 / 2 : ℝ) • euclideanBall (0 : Vec d) 1 := by
      dsimp only [BH]
      simpa only [translateSet_zero] using euclideanBall_eq_translateSet_smul_unit_of_pos
        (0 : Vec d) (show 0 < (1 / 2 : ℝ) by norm_num)
    rw [hBH, smul_smul]
    congr 1
    ring
  have hBackward : MeasurePreserving (fun x : Vec d => R⁻¹ • (x - z))
      (normalizedVolumeOn V) (normalizedVolumeOn BH) := by
    rw [← hHalfSet]
    exact (measurePreserving_inv_smul_normalizedVolumeOn_smul_set hR BH).comp
      (measurePreserving_subRight_normalizedVolumeOn_translateSet z (R • BH))
  have hGrad0Mean := memLp_normalizedVolumeOn_of_memLpOn hgrad0 hBHpos
  have hGradBackEq : (fun x => vecEuclideanNorm (u0.grad x)) ∘
      (fun x : Vec d => R⁻¹ • (x - z)) = fun x => vecEuclideanNorm (u.grad x) := by
    funext x
    simp only [Function.comp_apply, hGrad0Eq]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, sub_add_cancel]
  have hGradMean : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn V) := by
    have hh := hGrad0Mean.comp_measurePreserving hBackward
    rw [hGradBackEq] at hh
    exact hh
  have hGradRaw : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn V) := by
    rw [← volume_smul_normalizedVolumeOn_eq_volumeOn hVpos hVtop]
    exact hGradMean.smul_measure hVtop.ne
  have hGradNorm : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn V) =
      eLpNorm (fun x => vecEuclideanNorm (u0.grad x)) (ENNReal.ofReal p)
        (normalizedVolumeOn BH) := by
    have he := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
      hGrad0Mean.aestronglyMeasurable hBackward
    rw [hGradBackEq] at he
    exact he
  have hForceNorm : eLpNorm (fun x => vecEuclideanNorm (F0 x)) (ENNReal.ofReal p)
      (normalizedVolumeOn U) =
      eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (normalizedVolumeOn B) := by
    simpa only [F0, FR, Function.comp_apply] using!
      eLpNorm_comp_measurePreserving hFMean.aestronglyMeasurable hForward
  have hGradBMean := memLp_normalizedVolumeOn_of_memLpOn u.gradMemL2.memLp_vecEuclideanNorm hBpos
  have hGradU0Mean := memLp_normalizedVolumeOn_of_memLpOn u0.gradMemL2.memLp_vecEuclideanNorm hUpos
  have hEnergy : Real.sqrt (integralAverage U (fun x => vecNormSq (u0.grad x))) =
      Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) := by
    rw [sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two hGradU0Mean,
      sqrt_integralAverage_vecNormSq_eq_euclideanFieldLpMeanNormOn_two hGradBMean]
    change (eLpNorm (fun x => vecEuclideanNorm (u0.grad x)) 2 (normalizedVolumeOn U)).toReal =
      (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (normalizedVolumeOn B)).toReal
    rw [hGrad0Eq]
    exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hGradBMean.aestronglyMeasurable hForward)
  have hVB : V ⊆ B := euclideanBall_mono (by positivity) (by linarith)
  let v := u.restrict (isOpen_euclideanBall _ _) hVB
  have hcoord : GradMemLpOn V (ENNReal.ofReal p) v.grad := by
    intro i
    apply hGradRaw.of_le (v.gradMemL2 i).aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using!
      abs_apply_le_vecEuclideanNorm (u.grad x) i
  have hw := (v.toW1pOfGradMemLp hd (isOpenBoundedConvexDomain_euclideanBall z (by positivity))
    hVpos p hp hcoord).memW1p
  refine ⟨hw, hGradRaw, ?_⟩
  change (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn V)).toReal ≤ _
  rw [hGradNorm]
  change (eLpNorm (fun x => vecEuclideanNorm (u0.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn BH)).toReal ≤
      C * (Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) +
        p * (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (normalizedVolumeOn B)).toReal)
  change (eLpNorm (fun x => vecEuclideanNorm (u0.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn BH)).toReal ≤
      C * (Real.sqrt (integralAverage U (fun x => vecNormSq (u0.grad x))) +
        p * (eLpNorm (fun x => vecEuclideanNorm (F0 x)) (ENNReal.ofReal p) (normalizedVolumeOn U)).toReal) at hest0
  rw [hEnergy, hForceNorm] at hest0
  exact hest0

end
end PDE
