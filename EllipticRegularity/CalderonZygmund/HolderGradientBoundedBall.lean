module

public import EllipticRegularity.CalderonZygmund.HolderGradientBounded
public import PDEFoundation.PDE.AffineChange
public import PDEFoundation.Measure.DilationLp

/-! # Bounded gradients on arbitrary Hölder balls -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

/-- Hölder coefficients and forcing give an essentially bounded Euclidean
gradient on the concentric half ball at every positive scale. -/
theorem memLp_top_vecEuclideanNorm_grad_halfBall_of_holder_ball
    {d : ℕ} (hd : 0 < d) {Λ α R : ℝ} (hR : 0 < R)
    (hα0 : 0 < α) (hα1 : α < 1) (z : Vec d)
    (a : CoeffField d) (F : Vec d → Vec d)
    (hell : ∀ x ∈ euclideanBall z R, IsEllipticMatrix 1 Λ (a x))
    (ha : ∃ K : ℝ, 0 ≤ K ∧
      EuclideanMatrixHolderSeminormLE (euclideanBall z R) a α K)
    (hF : ∃ K : ℝ, 0 ≤ K ∧
      EuclideanFieldHolderSeminormLE (euclideanBall z R) F α K)
    (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F) :
    MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
      (volumeOn (euclideanBall z (R / 2))) := by
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
  have hell0 : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      IsEllipticMatrix 1 Λ (a0 x) := by
    intro x hx
    apply hell
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
    simpa [vecEuclideanNorm_smul, abs_of_pos hR, sub_eq_add_neg,
      add_assoc] using (mul_lt_mul_of_pos_left hx' hR)
  obtain ⟨Ka, hKa, haKa⟩ := ha
  have ha0 : ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE
      (euclideanBall (0 : Vec d) 1) a0 α K := by
    refine ⟨R ^ α * Ka, mul_nonneg (Real.rpow_nonneg hR.le _) hKa, ?_⟩
    intro x hx y hy ξ
    have hxR : R • x + z ∈ euclideanBall z R := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
      simpa [vecEuclideanNorm_smul, abs_of_pos hR] using
        mul_lt_mul_of_pos_left
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx) hR
    have hyR : R • y + z ∈ euclideanBall z R := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
      simpa [vecEuclideanNorm_smul, abs_of_pos hR] using
        mul_lt_mul_of_pos_left
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hy) hR
    have h := haKa (R • x + z) hxR (R • y + z) hyR ξ
    dsimp only [a0, aR]
    rw [show (R • x + z) - (R • y + z) = R • (x - y) by ext i; simp; ring,
      vecEuclideanNorm_smul, abs_of_pos hR, Real.mul_rpow hR.le
        (vecEuclideanNorm_nonneg _)] at h
    calc
      _ ≤ Ka * (R ^ α * vecEuclideanNorm (x - y) ^ α) *
          vecEuclideanNorm ξ := h
      _ = (R ^ α * Ka) * vecEuclideanNorm (x - y) ^ α *
          vecEuclideanNorm ξ := by ring
  obtain ⟨KF, hKF, hFKF⟩ := hF
  have hF0 : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE
      (euclideanBall (0 : Vec d) 1) F0 α K := by
    refine ⟨R ^ α * KF, mul_nonneg (Real.rpow_nonneg hR.le _) hKF, ?_⟩
    intro x hx y hy
    have hxR : R • x + z ∈ euclideanBall z R := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
      simpa [vecEuclideanNorm_smul, abs_of_pos hR] using
        mul_lt_mul_of_pos_left
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx) hR
    have hyR : R • y + z ∈ euclideanBall z R := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
      simpa [vecEuclideanNorm_smul, abs_of_pos hR] using
        mul_lt_mul_of_pos_left
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hy) hR
    have h := hFKF (R • x + z) hxR (R • y + z) hyR
    dsimp only [F0, FR]
    rw [show (R • x + z) - (R • y + z) = R • (x - y) by ext i; simp; ring,
      vecEuclideanNorm_smul, abs_of_pos hR, Real.mul_rpow hR.le
        (vecEuclideanNorm_nonneg _)] at h
    calc
      _ ≤ KF * (R ^ α * vecEuclideanNorm (x - y) ^ α) := h
      _ = (R ^ α * KF) * vecEuclideanNorm (x - y) ^ α := by ring
  have hgrad0 := memLp_top_vecEuclideanNorm_grad_halfBall_of_holder
    hd hα0 hα1 a0 F0 hell0 ha0 hF0 u0 hsol0
  have hgradEq : (fun x => vecEuclideanNorm (u0.grad x)) =
      fun x => vecEuclideanNorm (u.grad (R • x + z)) := by
    funext x
    simp only [u0, usraw, uR, uraw, H1Function.restrict_grad,
      H1Function.dilate_grad, H1Function.translate_grad]
    congr 2
    ext i
    simp
  rw [hgradEq] at hgrad0
  let Bhalf := euclideanBall (0 : Vec d) (1 / 2)
  have hscaled : MemLp (fun x => vecEuclideanNorm (u.grad (x + z))) ∞
      (volumeOn (R • Bhalf)) := by
    have hcTop : ENNReal.ofReal (R ^ d) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hh : MemLp (fun x => vecEuclideanNorm (u.grad (R • x + z))) ∞
        (ENNReal.ofReal (R ^ d) • volumeOn Bhalf) :=
      hgrad0.smul_measure hcTop
    have hp := hh.comp_measurePreserving
      (measurePreserving_inv_smul_restrict_smul_set hR Bhalf)
    have hfun :
        (fun x => vecEuclideanNorm (u.grad (R • x + z))) ∘
            (fun x : Vec d => R⁻¹ • x) =
          fun x => vecEuclideanNorm (u.grad (x + z)) := by
      funext x
      dsimp only [Function.comp_apply]
      have hx : R • (R⁻¹ • x) + z = x + z := by
        ext i
        dsimp
        field_simp
      rw [hx]
    rw [hfun] at hp
    exact hp
  have htranslated := hscaled.comp_measurePreserving
    (measurePreserving_subRight_restrict_translateSet z (R • Bhalf))
  have hhalfset : translateSet z (R • Bhalf) = euclideanBall z (R / 2) := by
    rw [euclideanBall_eq_translateSet_smul_unit_of_pos z
      (div_pos hR (by norm_num))]
    congr 1
    have hBhalf : Bhalf = (1 / 2 : ℝ) • euclideanBall (0 : Vec d) 1 := by
      dsimp only [Bhalf]
      simpa only [translateSet_zero] using
        euclideanBall_eq_translateSet_smul_unit_of_pos (0 : Vec d)
          (show 0 < (1 / 2 : ℝ) by norm_num)
    rw [hBhalf]
    rw [smul_smul]
    congr 1
    ring
  rw [hhalfset] at htranslated
  have hfun :
      (fun x => vecEuclideanNorm (u.grad (x + z))) ∘
          (fun x : Vec d => x - z) =
        fun x => vecEuclideanNorm (u.grad x) := by
    funext x
    dsimp only [Function.comp_apply]
    rw [sub_add_cancel]
  rw [hfun] at htranslated
  exact htranslated

end

end PDE
