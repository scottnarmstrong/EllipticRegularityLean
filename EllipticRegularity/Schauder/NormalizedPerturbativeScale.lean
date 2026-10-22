module

public import EllipticRegularity.Schauder.LocalGradient
public import PDEFoundation.Regularity.EllipticContinuousCoefficient
public import PDEFoundation.Sobolev.H1.EllipticForcingScale
public import PDEFoundation.PDE.HolderNormalizedEquation

/-! # Perturbative gradient scale after elliptic normalization -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The actual local perturbative estimate on the inner normalized ball. All
coefficient and forcing hypotheses are stated in the original coordinates. -/
theorem normalized_perturbative_gradient_scale
    (hd : 2 ≤ d) {z : Vec d} {R alpha delta M Lam : ℝ}
    (hR : 0 < R) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - alpha))
    (hM : 0 ≤ M) {a : CoeffField d}
    (haCont : ContinuousOn a (euclideanBall z R))
    (hAz : IsEllipticMatrix 1 Lam (a z))
    (hclose : ∀ x ∈ euclideanBall z R,
      IsMatrixPerturbationLE delta (a x) (a z))
    {F : Vec d → Vec d} (hF : MemVectorL2On (euclideanBall z R) F)
    (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (hforce : ∀ q : ℝ, 0 < q → q ≤ R →
      q ^ (1 - alpha) *
        Real.sqrt (integralAverage (euclideanBall z q)
          (fun x => vecNormSq (F x))) ≤ M) :
    let e := ellipticNormalizerContinuousLinearEquiv hAz
    let rho := R / Real.sqrt Lam
    let Y := euclideanBall (e z) rho
    let hY : Y ⊆ e '' euclideanBall z R :=
      euclideanBall_subset_ellipticNormalizer_image hAz hR z
    let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
    let L := Real.sqrt ((Real.sqrt Lam) ^ d)
    let D := (2 : ℝ) ^ ((d : ℝ) / 2)
    ∀ s : ℝ, 0 < s → s ≤ rho →
      s ^ (1 - alpha) *
        Real.sqrt (integralAverage (euclideanBall (e z) s)
          (fun y => vecNormSq (v.grad y))) ≤
        D * (rho ^ (1 - alpha) *
          Real.sqrt (integralAverage Y (fun y => vecNormSq (v.grad y))) +
          8 * (D * (L * M)) / (1 - alpha)) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hAz
  let T := ellipticNormalizer (a z)
  let rho := R / Real.sqrt Lam
  let Y := euclideanBall (e z) rho
  have hY : Y ⊆ e '' euclideanBall z R :=
    euclideanBall_subset_ellipticNormalizer_image hAz hR z
  let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
  let b : CoeffField d := fun y =>
    T * (a (e.symm y) - skewPart (a z)) * matTranspose T
  let F' : Vec d → Vec d := fun y => matVecMul T (F (e.symm y))
  let L := Real.sqrt ((Real.sqrt Lam) ^ d)
  let D := (2 : ℝ) ^ ((d : ℝ) / 2)
  have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hAz.Lam_pos
  have hrho : 0 < rho := div_pos hR hsqrt
  have hImageCont := ellipticNormalizedCoefficient_continuousOn hAz haCont
  have hbCont : ContinuousOn b Y := by
    exact hImageCont.mono hY
  have hbMeas : ∀ i j, AEMeasurable (fun y => b y i j) (volumeOn Y) := by
    intro i j
    have hij := (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hbCont)
    change ContinuousOn (fun y => b y i j) Y at hij
    exact (hij.aestronglyMeasurable (μ := volume)
      (isOpen_euclideanBall _ _).measurableSet).aemeasurable
  have hbClosePoint : ∀ y ∈ Y, IsMatrixPerturbationLE delta (b y) 1 := by
    intro y hy
    exact ellipticNormalizedCoefficient_isMatrixPerturbationLE hAz hdelta hclose y (hY hy)
  have hbClose : ∀ᵐ y ∂volumeOn Y, IsMatrixPerturbationLE delta (b y) 1 := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall _ _).measurableSet] with y hy
    exact hbClosePoint y hy
  have hFscale := ellipticNormalizer_forcing_scale hAz hR z hF
  have hF' : MemVectorL2On Y F' := by
    simpa only [Y, rho, e, T, F'] using hFscale.1
  have hvSol : IsWeakDivergenceFormSolutionOn b Y v 0 F' := by
    simpa only [b, Y, v, F', e, T, hY] using
      hsol.ellipticNormalize_innerBall hR hAz
  have hLam : 1 ≤ Lam := hAz.lam_le_Lam
  have hsqrtOne : 1 ≤ Real.sqrt Lam := by
    simpa using Real.sqrt_le_sqrt hLam
  have hgap : 0 < 1 - alpha := sub_pos.mpr halpha1
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hLM : 0 ≤ L * M := mul_nonneg hL hM
  have hforce' : ∀ s : ℝ, 0 < s → s ≤ rho →
      s ^ (1 - alpha) *
        Real.sqrt (integralAverage (euclideanBall (e z) s)
          (fun y => vecNormSq (F' y))) ≤ L * M := by
    intro s hs hsrho
    let q := Real.sqrt Lam * s
    have hq : 0 < q := mul_pos hsqrt hs
    have hqR : q ≤ R := by
      have hm := mul_le_mul_of_nonneg_left hsrho hsqrt.le
      dsimp [rho] at hm
      dsimp [q]
      calc
        Real.sqrt Lam * s ≤ Real.sqrt Lam * (R / Real.sqrt Lam) := hm
        _ = R := by field_simp [hsqrt.ne']
    have hsq : s ≤ q := by
      dsimp [q]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrtOne hs.le
    have hpow : s ^ (1 - alpha) ≤ q ^ (1 - alpha) :=
      Real.rpow_le_rpow hs.le hsq hgap.le
    have hscale := hFscale.2 s hs hsrho
    calc
      _ ≤ s ^ (1 - alpha) * (L *
          Real.sqrt (integralAverage (euclideanBall z q)
            (fun x => vecNormSq (F x)))) :=
        mul_le_mul_of_nonneg_left (by simpa only [L, e, T, F', q] using hscale)
          (Real.rpow_nonneg hs.le _)
      _ = L * (s ^ (1 - alpha) *
          Real.sqrt (integralAverage (euclideanBall z q)
            (fun x => vecNormSq (F x)))) := by ring
      _ ≤ L * (q ^ (1 - alpha) *
          Real.sqrt (integralAverage (euclideanBall z q)
            (fun x => vecNormSq (F x)))) := by
        gcongr
      _ ≤ L * M := mul_le_mul_of_nonneg_left (hforce q hq hqR) hL
  have hbound := schauder_local_gradient_bound_of_forcing_scale
    (lt_of_lt_of_le (by norm_num) hd) hrho halpha0 halpha1 hdelta hsmall
    hLM v hbMeas hbClose hF' hvSol hforce'
  simpa only [Y, rho, L, D, e, v] using hbound

end

end PDE
