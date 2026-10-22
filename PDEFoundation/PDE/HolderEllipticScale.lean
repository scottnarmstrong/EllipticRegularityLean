module

public import PDEFoundation.PDE.HolderEllipticSmallScale
public import PDEFoundation.Sobolev.H1.EllipticOuterRadii

/-! # All-radius local Hölder gradient bounds -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The small normalized radii and the outer restriction radii combine into
one quantitative estimate with a constant depending only on `d` and `Lam`. -/
theorem exists_holder_elliptic_scale_constant [NeZero d]
    (hd : 2 ≤ d) (Lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {z : Vec d} {R alpha Ka KF : ℝ},
      0 < R → 0 < alpha → alpha < 1 → 0 ≤ Ka → 0 ≤ KF →
      ∀ {a : CoeffField d} {F : Vec d → Vec d},
      (∀ x ∈ euclideanBall z R, IsEllipticMatrix 1 Lam (a x)) →
      EuclideanMatrixHolderSeminormLE (euclideanBall z R) a alpha Ka →
      EuclideanFieldHolderSeminormLE (euclideanBall z R) F alpha KF →
      ∀ u : H1Function (euclideanBall z R),
      IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F →
      (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ alpha * Ka ≤
        alpha * (1 - alpha) /
          (32 * (1 + (2 : ℝ) ^ ((d : ℝ) / 2))) →
      ∀ r : ℝ, 0 < r → r ≤ R →
        Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (u.grad x))) ≤
          (C / alpha) *
            (Real.sqrt (integralAverage (euclideanBall z R)
              (fun x => vecNormSq (u.grad x))) +
              R ^ alpha * KF / (1 - alpha)) ∧
        (R / r) ^ alpha * centeredVectorMeanL2
            (euclideanBall z r) u.grad ≤
          (C / alpha) *
            (Real.sqrt (integralAverage (euclideanBall z R)
              (fun x => vecNormSq (u.grad x))) +
              R ^ alpha * KF / (1 - alpha)) := by
  let L := Real.sqrt ((Real.sqrt Lam) ^ d)
  let D := (2 : ℝ) ^ ((d : ℝ) / 2)
  let H := 1 + 2 * D
  let J := 2 * L * Real.sqrt Lam + H
  let C := 1 + L * 40 * D * (1 + D) * J +
    L * Real.sqrt Lam * 16 * D * J + Real.sqrt Lam * L
  refine ⟨C, ?_, ?_⟩
  · have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
    have hJ : 0 ≤ J := by dsimp [J, H]; positivity
    dsimp [C]
    positivity
  · intro z R alpha Ka KF hR ha0 ha1 hKa hKF a F hell ha hF u hsol hsmall r hr hrR
    let rho := R / Real.sqrt Lam
    let M0 := Real.sqrt (integralAverage (euclideanBall z R)
      (fun x => vecNormSq (u.grad x)))
    let W := R ^ alpha * KF / (1 - alpha)
    let S := M0 + W
    let Q := 2 * L * Real.sqrt Lam * M0 + H * W
    have hAz := hell z (center_mem_euclideanBall z hR)
    have hLam : 1 ≤ Lam := hAz.lam_le_Lam
    have hsqrt : 1 ≤ Real.sqrt Lam := by simpa using Real.sqrt_le_sqrt hLam
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hgap : 0 < 1 - alpha := sub_pos.mpr ha1
    have hM0 : 0 ≤ M0 := Real.sqrt_nonneg _
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have hS : 0 ≤ S := add_nonneg hM0 hW
    have hQJ : Q ≤ J * S := by
      have hc1 : 0 ≤ (2 * L * Real.sqrt Lam) * W := by positivity
      have hc2 : 0 ≤ H * M0 := mul_nonneg hH hM0
      dsimp only [Q, J, S]
      calc
        _ ≤ 2 * L * Real.sqrt Lam * M0 + H * W +
            (2 * L * Real.sqrt Lam) * W + H * M0 := by linarith
        _ = (2 * L * Real.sqrt Lam + H) * (M0 + W) := by ring
    have hCnonneg : 0 ≤ C := (show 0 < C by
      have : 0 < C := by dsimp [C]; positivity
      exact this).le
    have htermA : 0 ≤ L * 40 * D * (1 + D) * J := by positivity
    have htermB : 0 ≤ L * Real.sqrt Lam * 16 * D * J := by positivity
    have htermS : 0 ≤ Real.sqrt Lam * L := by positivity
    have hsLC : Real.sqrt Lam * L ≤ C := by
      dsimp [C]
      linarith
    have hLC : L ≤ C := by
      have : L ≤ Real.sqrt Lam * L := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt hL
      exact this.trans hsLC
    have halphaInv : 1 ≤ alpha⁻¹ := (one_le_inv₀ ha0).2 ha1.le
    have hCinflate : C * S ≤ (C / alpha) * S := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left halphaInv hCnonneg) hS
    by_cases hsmallr : r ≤ rho
    · have hs := holder_elliptic_smallScale_bound hd hR ha0 ha1 hKa hKF
        hell ha hF u hsol hsmall r hr hsmallr
      have hsqrtPow : Real.sqrt Lam ^ alpha ≤ Real.sqrt Lam := by
        calc
          Real.sqrt Lam ^ alpha ≤ Real.sqrt Lam ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hsqrt ha1.le
          _ = Real.sqrt Lam := Real.rpow_one _
      constructor
      · calc
          _ ≤ L * (40 * D * (1 + D) / alpha) * Q := by
            convert hs.1 using 1
            all_goals (dsimp [L, D, H, M0, W, Q, rho]; ring)
          _ ≤ (C / alpha) * S := by
            have hcoef : L * 40 * D * (1 + D) * J ≤ C := by
              dsimp [C]
              linarith
            calc
              _ ≤ L * (40 * D * (1 + D) / alpha) * (J * S) :=
                mul_le_mul_of_nonneg_left hQJ (by positivity)
              _ = (L * 40 * D * (1 + D) * J / alpha) * S := by ring
              _ ≤ (C / alpha) * S :=
                mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right hcoef ha0.le) hS
      · calc
          _ ≤ L * Real.sqrt Lam ^ alpha * 16 * D * Q := by
            convert hs.2 using 1
            all_goals (dsimp [L, D, H, M0, W, Q, rho]; ring)
          _ ≤ L * Real.sqrt Lam * 16 * D * (J * S) := by
            gcongr
          _ = (L * Real.sqrt Lam * 16 * D * J) * S := by ring
          _ ≤ C * S := by
            apply mul_le_mul_of_nonneg_right _ hS
            dsimp [C]
            linarith
          _ ≤ (C / alpha) * S := hCinflate
    · have hrho : rho ≤ r := le_of_not_ge hsmallr
      have hsub : euclideanBall z r ⊆ euclideanBall z R :=
        euclideanBall_mono hr.le hrR
      have hmean := sqrt_integralAverage_vecNormSq_mono_set hsub
        (volume_euclideanBall_toReal_pos z hR) u.gradMemL2
      have hratio : R / r ≤ Real.sqrt Lam := by
        apply (div_le_iff₀ hr).2
        have hm := mul_le_mul_of_nonneg_right hrho (zero_le_one.trans hsqrt)
        dsimp [rho] at hm
        field_simp [(lt_of_lt_of_le zero_lt_one hsqrt).ne'] at hm
        simpa [mul_comm] using hm
      have hvol : Real.sqrt (volume (euclideanBall z R)).toReal /
          Real.sqrt (volume (euclideanBall z r)).toReal ≤ L := by
        rw [← Real.sqrt_div ENNReal.toReal_nonneg,
          volume_euclideanBall_toReal_div_eq_div_pow z z hr hR]
        exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (div_nonneg hR.le hr.le) hratio d)
      have henergy : Real.sqrt (integralAverage (euclideanBall z r)
          (fun x => vecNormSq (u.grad x))) ≤ L * M0 :=
        hmean.trans (mul_le_mul_of_nonneg_right hvol hM0)
      have hgrad : MemVectorL2On (euclideanBall z r) u.grad := fun i =>
        (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
      have hcenter := centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq hgrad
        (volume_euclideanBall_pos z hr)
        (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hr.le))
      have hweight : (R / r) ^ alpha ≤ Real.sqrt Lam :=
        (Real.rpow_le_rpow_of_exponent_le
          (by exact (le_div_iff₀ hr).2 (by simpa only [one_mul] using hrR)) ha1.le).trans_eq (Real.rpow_one _)
          |>.trans hratio
      constructor
      · calc
          _ ≤ L * M0 := henergy
          _ ≤ C * S := by
            calc
              L * M0 ≤ C * M0 := mul_le_mul_of_nonneg_right hLC hM0
              _ ≤ C * S := mul_le_mul_of_nonneg_left (by dsimp [S]; linarith) hCnonneg
          _ ≤ (C / alpha) * S := hCinflate
      · calc
          _ ≤ Real.sqrt Lam * (L * M0) :=
            mul_le_mul hweight (hcenter.trans henergy) (Real.sqrt_nonneg _) (by positivity)
          _ ≤ C * S := by
            calc
              Real.sqrt Lam * (L * M0) = (Real.sqrt Lam * L) * M0 := by ring
              _ ≤ C * M0 := mul_le_mul_of_nonneg_right hsLC hM0
              _ ≤ C * S := mul_le_mul_of_nonneg_left (by dsimp [S]; linarith) hCnonneg
          _ ≤ (C / alpha) * S := hCinflate

end

end PDE
