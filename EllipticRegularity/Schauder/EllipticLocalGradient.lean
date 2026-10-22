module

public import EllipticRegularity.Schauder.NormalizedPerturbativeScale
public import PDEFoundation.Sobolev.H1.EllipticGradientPullback
public import PDEFoundation.Sobolev.H1.EllipticBallEnergy
public import PDEFoundation.Sobolev.H1.EllipticOuterRadii

/-! # Local gradient scale in the original elliptic coordinates -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The normalized perturbative estimate and the elliptic coordinate bounds
combine into an all-radius estimate in the original coordinates. -/
theorem exists_elliptic_local_gradient_constant
    (hd : 2 ≤ d) (Lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {z : Vec d} {R alpha delta M : ℝ},
      0 < R → 0 < alpha → alpha < 1 → 0 ≤ delta →
      delta ≤ (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - alpha) →
      0 ≤ M →
      ∀ {a : CoeffField d}, ContinuousOn a (euclideanBall z R) →
      ∀ (_hAz : IsEllipticMatrix 1 Lam (a z)),
      (∀ x ∈ euclideanBall z R,
        IsMatrixPerturbationLE delta (a x) (a z)) →
      ∀ {F : Vec d → Vec d}, MemVectorL2On (euclideanBall z R) F →
      ∀ u : H1Function (euclideanBall z R),
      IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F →
      (∀ q : ℝ, 0 < q → q ≤ R →
        q ^ (1 - alpha) *
          Real.sqrt (integralAverage (euclideanBall z q)
            (fun x => vecNormSq (F x))) ≤ M) →
      ∀ r : ℝ, 0 < r → r ≤ R →
        r ^ (1 - alpha) *
          Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (u.grad x))) ≤
          C * (R ^ (1 - alpha) *
            Real.sqrt (integralAverage (euclideanBall z R)
              (fun x => vecNormSq (u.grad x))) + M / (1 - alpha)) := by
  let L := Real.sqrt ((Real.sqrt Lam) ^ d)
  let D := (2 : ℝ) ^ ((d : ℝ) / 2)
  let C := 1 + L ^ 2 * Real.sqrt Lam * D + 8 * L ^ 2 * D ^ 2 + L
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, L, D]
    positivity
  · intro z R alpha delta M hR halpha0 halpha1 hdelta hsmall hM
      a haCont hAz hclose F hF u hsol hforce r hr hrR
    let e := ellipticNormalizerContinuousLinearEquiv hAz
    let rho := R / Real.sqrt Lam
    let Y := euclideanBall (e z) rho
    have hY : Y ⊆ e '' euclideanBall z R :=
      euclideanBall_subset_ellipticNormalizer_image hAz hR z
    let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hY
    let M0 := Real.sqrt (integralAverage (euclideanBall z R)
      (fun x => vecNormSq (u.grad x)))
    let S := R ^ (1 - alpha) * M0 + M / (1 - alpha)
    have hsqrt : 0 < Real.sqrt Lam := Real.sqrt_pos.mpr hAz.Lam_pos
    have hrho : 0 < rho := div_pos hR hsqrt
    have hgap : 0 < 1 - alpha := sub_pos.mpr halpha1
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
    have hM0 : 0 ≤ M0 := Real.sqrt_nonneg _
    have hRpow : 0 ≤ R ^ (1 - alpha) := Real.rpow_nonneg hR.le _
    have hMgap : 0 ≤ M / (1 - alpha) := div_nonneg hM hgap.le
    have hS : 0 ≤ S := add_nonneg (mul_nonneg hRpow hM0) hMgap
    have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
    have hCL : L ≤ C := by
      dsimp [C]
      have h1 : 0 ≤ L ^ 2 * Real.sqrt Lam * D := by positivity
      have h2 : 0 ≤ 8 * L ^ 2 * D ^ 2 := by positivity
      linarith
    by_cases hrrho : r ≤ rho
    · have hnorm := normalized_perturbative_gradient_scale hd hR halpha0
        halpha1 hdelta hsmall hM haCont hAz hclose hF u hsol hforce r hr hrrho
      have hpull := (ellipticNormalizer_restrictedGradient_mean_bounds
        hAz hR z u).2 r hr hrrho |>.2
      have hinner := sqrt_integralAverage_ellipticNormalizer_inner_grad_le
        hAz hR z u
      have hM0v : Real.sqrt (integralAverage Y
          (fun y => vecNormSq (v.grad y))) ≤ L * Real.sqrt Lam * M0 := by
        simpa only [Y, rho, v, e, L, M0, H1Function.restrict_grad] using hinner
      have hrhopow : rho ^ (1 - alpha) ≤ R ^ (1 - alpha) := by
        have hsqrtOne : 1 ≤ Real.sqrt Lam := by
          simpa using Real.sqrt_le_sqrt hAz.lam_le_Lam
        have hrhoR : rho ≤ R := by
          dsimp [rho]
          exact div_le_self hR.le hsqrtOne
        exact Real.rpow_le_rpow (div_nonneg hR.le hsqrt.le) hrhoR hgap.le
      calc
        r ^ (1 - alpha) * Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (u.grad x))) ≤
            L * (r ^ (1 - alpha) *
              Real.sqrt (integralAverage (euclideanBall (e z) r)
                (fun y => vecNormSq (v.grad y)))) := by
          calc
            _ ≤ r ^ (1 - alpha) * (L *
                Real.sqrt (integralAverage (euclideanBall (e z) r)
                  (fun y => vecNormSq (v.grad y)))) :=
              mul_le_mul_of_nonneg_left (by simpa only [L] using hpull)
                (Real.rpow_nonneg hr.le _)
            _ = _ := by ring
        _ ≤ L * (D * (rho ^ (1 - alpha) *
              Real.sqrt (integralAverage Y (fun y => vecNormSq (v.grad y))) +
              8 * (D * (L * M)) / (1 - alpha))) :=
          mul_le_mul_of_nonneg_left (by simpa only [L, D, rho, Y, v, e] using hnorm) hL
        _ ≤ (L ^ 2 * Real.sqrt Lam * D) * (R ^ (1 - alpha) * M0) +
              (8 * L ^ 2 * D ^ 2) * (M / (1 - alpha)) := by
          have hi : rho ^ (1 - alpha) *
              Real.sqrt (integralAverage Y (fun y => vecNormSq (v.grad y))) ≤
              R ^ (1 - alpha) * (L * Real.sqrt Lam * M0) :=
            mul_le_mul hrhopow hM0v (Real.sqrt_nonneg _) hRpow
          calc
            L * (D * (rho ^ (1 - alpha) *
                Real.sqrt (integralAverage Y (fun y => vecNormSq (v.grad y))) +
              8 * (D * (L * M)) / (1 - alpha))) =
                L * (D * (rho ^ (1 - alpha) *
                  Real.sqrt (integralAverage Y (fun y => vecNormSq (v.grad y))))) +
                L * (D * (8 * (D * (L * M)) / (1 - alpha))) := by ring
            _ ≤ (L ^ 2 * Real.sqrt Lam * D) * (R ^ (1 - alpha) * M0) +
                (8 * L ^ 2 * D ^ 2) * (M / (1 - alpha)) := by
              apply add_le_add
              · calc
                  L * (D * (rho ^ (1 - alpha) *
                      Real.sqrt (integralAverage Y (fun y => vecNormSq (v.grad y))))) ≤
                      L * (D * (R ^ (1 - alpha) * (L * Real.sqrt Lam * M0))) := by
                    gcongr
                  _ = (L ^ 2 * Real.sqrt Lam * D) * (R ^ (1 - alpha) * M0) := by ring
              · ring_nf
                exact le_rfl
        _ ≤ C * S := by
          have hc1 : L ^ 2 * Real.sqrt Lam * D ≤ C := by
            dsimp [C]
            have h1 : 0 ≤ 8 * L ^ 2 * D ^ 2 := by positivity
            linarith [hL]
          have hc2 : 8 * L ^ 2 * D ^ 2 ≤ C := by
            dsimp [C]
            have h1 : 0 ≤ L ^ 2 * Real.sqrt Lam * D := by positivity
            linarith [hL]
          calc
            _ ≤ C * (R ^ (1 - alpha) * M0) + C * (M / (1 - alpha)) :=
              add_le_add
                (mul_le_mul_of_nonneg_right hc1 (mul_nonneg hRpow hM0))
                (mul_le_mul_of_nonneg_right hc2 hMgap)
            _ = C * S := by dsimp [S]; ring
    · have hrho' : rho ≤ r := le_of_not_ge hrrho
      have hsub : euclideanBall z r ⊆ euclideanBall z R :=
        euclideanBall_mono hr.le hrR
      have hmean := sqrt_integralAverage_vecNormSq_mono_set hsub
        (volume_euclideanBall_toReal_pos z hR) u.gradMemL2
      have hratio : R / r ≤ Real.sqrt Lam := by
        apply (div_le_iff₀ hr).2
        have hm := mul_le_mul_of_nonneg_right hrho' hsqrt.le
        dsimp [rho] at hm
        field_simp [hsqrt.ne'] at hm
        simpa only [mul_comm] using hm
      have hvol : Real.sqrt (volume (euclideanBall z R)).toReal /
          Real.sqrt (volume (euclideanBall z r)).toReal ≤ L := by
        rw [← Real.sqrt_div ENNReal.toReal_nonneg,
          volume_euclideanBall_toReal_div_eq_div_pow z z hr hR]
        exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (div_nonneg hR.le hr.le) hratio d)
      have henergy : Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x))) ≤ L * M0 :=
        hmean.trans (mul_le_mul_of_nonneg_right hvol hM0)
      have hrpow : r ^ (1 - alpha) ≤ R ^ (1 - alpha) :=
        Real.rpow_le_rpow hr.le hrR hgap.le
      calc
        _ ≤ R ^ (1 - alpha) * (L * M0) :=
          mul_le_mul hrpow henergy (Real.sqrt_nonneg _) hRpow
        _ = L * (R ^ (1 - alpha) * M0) := by ring
        _ ≤ C * (R ^ (1 - alpha) * M0) :=
          mul_le_mul_of_nonneg_right hCL (mul_nonneg hRpow hM0)
        _ ≤ C * S := by
          apply mul_le_mul_of_nonneg_left _ hCnonneg
          dsimp [S]
          linarith

end

end PDE
