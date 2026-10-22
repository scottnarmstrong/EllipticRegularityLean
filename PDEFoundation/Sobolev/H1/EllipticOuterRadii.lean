module

public import PDEFoundation.Sobolev.H1.MeanEnergy
public import PDEFoundation.Sobolev.H1.VectorMeanRestriction
public import PDEFoundation.Ambient.CoefficientField

/-!
# Gradient mean bounds on outer elliptic radii
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Between the elliptic inner radius `R / sqrt Lam` and `R`, restriction of
gradient mean energy costs only the displayed elliptic volume factor. -/
theorem elliptic_outer_radii_gradient_mean_bounds
    {A : Mat d} {Lam R alpha r : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hR : 0 < R) (_halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hrlower : R / Real.sqrt Lam ≤ r) (hrupper : r ≤ R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) :
    let L := Real.sqrt ((Real.sqrt Lam) ^ d)
    Real.sqrt (integralAverage (euclideanBall (0 : Vec d) r)
        (fun x => vecNormSq (u.grad x))) ≤
        L * Real.sqrt (integralAverage (euclideanBall (0 : Vec d) R)
          (fun x => vecNormSq (u.grad x))) ∧
      (R / r) ^ alpha *
          centeredVectorMeanL2 (euclideanBall (0 : Vec d) r) u.grad ≤
        Real.sqrt Lam * L *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec d) R)
            (fun x => vecNormSq (u.grad x))) := by
  dsimp only
  have hLam : 1 ≤ Lam := hA.lam_le_Lam
  have hsqrtLam : 1 ≤ Real.sqrt Lam := by
    simpa using Real.sqrt_le_sqrt hLam
  have hr : 0 < r := lt_of_lt_of_le
    (div_pos hR (lt_of_lt_of_le zero_lt_one hsqrtLam)) hrlower
  have hratioNonneg : 0 ≤ R / r := div_nonneg hR.le hr.le
  have hratioOne : 1 ≤ R / r := (le_div_iff₀ hr).2 (by simpa using hrupper)
  have hratioLam : R / r ≤ Real.sqrt Lam := by
    apply (div_le_iff₀ hr).2
    have hm := mul_le_mul_of_nonneg_right hrlower (zero_le_one.trans hsqrtLam)
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hsqrtLam)] at hm
    simpa only [mul_comm] using hm
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall 0 R :=
    euclideanBall_mono hr.le hrupper
  have hrestrict := sqrt_integralAverage_vecNormSq_mono_set hsub
    (volume_euclideanBall_toReal_pos (0 : Vec d) hR) u.gradMemL2
  have hvolume :
      Real.sqrt (volume (euclideanBall (0 : Vec d) R)).toReal /
          Real.sqrt (volume (euclideanBall (0 : Vec d) r)).toReal ≤
        Real.sqrt ((Real.sqrt Lam) ^ d) := by
    rw [← Real.sqrt_div ENNReal.toReal_nonneg,
      volume_euclideanBall_toReal_div_eq_div_pow (0 : Vec d) 0 hr hR]
    apply Real.sqrt_le_sqrt
    exact pow_le_pow_left₀ hratioNonneg hratioLam d
  have henergy :
      Real.sqrt (integralAverage (euclideanBall (0 : Vec d) r)
          (fun x => vecNormSq (u.grad x))) ≤
        Real.sqrt ((Real.sqrt Lam) ^ d) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec d) R)
            (fun x => vecNormSq (u.grad x))) :=
    hrestrict.trans (mul_le_mul_of_nonneg_right hvolume (Real.sqrt_nonneg _))
  have hgradSmall : MemVectorL2On (euclideanBall (0 : Vec d) r) u.grad :=
    fun i => (u.gradMemL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hcenter := centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq
    hgradSmall (volume_euclideanBall_pos (0 : Vec d) hr)
    (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top (0 : Vec d) hr.le))
  have hweight : (R / r) ^ alpha ≤ Real.sqrt Lam := by
    calc
      (R / r) ^ alpha ≤ (R / r) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hratioOne halpha1.le
      _ = R / r := Real.rpow_one _
      _ ≤ Real.sqrt Lam := hratioLam
  refine ⟨henergy, ?_⟩
  calc
    (R / r) ^ alpha * centeredVectorMeanL2 (euclideanBall (0 : Vec d) r) u.grad ≤
        (R / r) ^ alpha *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec d) r)
            (fun x => vecNormSq (u.grad x))) :=
      mul_le_mul_of_nonneg_left hcenter (Real.rpow_nonneg hratioNonneg alpha)
    _ ≤ Real.sqrt Lam *
          (Real.sqrt ((Real.sqrt Lam) ^ d) *
            Real.sqrt (integralAverage (euclideanBall (0 : Vec d) R)
              (fun x => vecNormSq (u.grad x)))) :=
      mul_le_mul hweight henergy (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

end

end PDE
