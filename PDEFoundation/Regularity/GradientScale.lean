module

public import PDEFoundation.Analysis.DyadicRadius
public import PDEFoundation.Sobolev.H1.MeanEnergy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Arbitrary-radius readout of a dyadic gradient-scale estimate

The exact scaling of round-ball volume transfers the dyadic estimate to every
intermediate radius at the dimension-only cost `2 ^ (d / 2)`.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The ratio of square-root volumes of nested round balls whose radii differ
by at most a factor of two. -/
theorem sqrt_volume_ratio_euclideanBall_le_two_rpow
    (z : Vec d) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hts : t ≤ 2 * s) :
    Real.sqrt (volume (euclideanBall z t)).toReal /
        Real.sqrt (volume (euclideanBall z s)).toReal ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) := by
  have hratio :
      (volume (euclideanBall z t)).toReal /
          (volume (euclideanBall z s)).toReal = (t / s) ^ d :=
    volume_euclideanBall_toReal_div_eq_div_pow z z hs ht
  have hts' : t / s ≤ 2 := (div_le_iff₀ hs).2 hts
  have hratio0 : 0 ≤ t / s := div_nonneg ht.le hs.le
  have hpow : (t / s) ^ d ≤ (2 : ℝ) ^ d :=
    pow_le_pow_left₀ hratio0 hts' d
  rw [← Real.sqrt_div ENNReal.toReal_nonneg,
    volume_euclideanBall_toReal_div_eq_div_pow z z hs ht]
  calc
    Real.sqrt ((t / s) ^ d) ≤ Real.sqrt ((2 : ℝ) ^ d) :=
      Real.sqrt_le_sqrt hpow
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- Every smaller positive radius lies between two consecutive dyadic radii;
the dyadic weighted mean-energy bound therefore controls every radius up to
the dimension-only round-ball volume factor. -/
theorem sqrt_integralAverage_vecNormSq_of_dyadic_scale_bound
    (z : Vec d) {R α K : ℝ} (hR : 0 < R) (hα : α < 1)
    {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hdyadic : ∀ n : ℕ,
      dyadicRadius R n ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
            (fun x => vecNormSq (F x))) ≤ K) :
    ∀ s : ℝ, 0 < s → s ≤ R →
      s ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z s)
            (fun x => vecNormSq (F x))) ≤
        (2 : ℝ) ^ ((d : ℝ) / 2) * K := by
  intro s hs hsR
  obtain ⟨n, hlow, hhigh⟩ := exists_dyadicRadius_bracket hR hs hsR
  let t : ℝ := dyadicRadius R n
  have ht : 0 < t := by
    dsimp [t]
    exact dyadicRadius_pos hR n
  have hst : s ≤ t := hhigh
  have hhalf : t / 2 < s := by
    have hlow' := hlow
    rw [dyadicRadius_succ] at hlow'
    simpa only [t] using hlow'
  have hts : t ≤ 2 * s := by linarith only [hhalf]
  have htR : t ≤ R := by
    dsimp [t]
    exact dyadicRadius_le hR.le n
  have hsub_st : euclideanBall z s ⊆ euclideanBall z t :=
    euclideanBall_mono hs.le hst
  have hsub_tR : euclideanBall z t ⊆ euclideanBall z R :=
    euclideanBall_mono ht.le htR
  have hFt : MemVectorL2On (euclideanBall z t) F :=
    gradMemLpOn_mono hsub_tR hF
  have hvolt : 0 < (volume (euclideanBall z t)).toReal :=
    volume_euclideanBall_toReal_pos z ht
  have hmean_mono :=
    sqrt_integralAverage_vecNormSq_mono_set hsub_st hvolt hFt
  have hvolume_ratio :=
    sqrt_volume_ratio_euclideanBall_le_two_rpow z hs ht hts
  have hmean_bound :
      Real.sqrt (integralAverage (euclideanBall z s)
          (fun x => vecNormSq (F x))) ≤
        (2 : ℝ) ^ ((d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall z t)
            (fun x => vecNormSq (F x))) := by
    exact hmean_mono.trans
      (mul_le_mul_of_nonneg_right hvolume_ratio (Real.sqrt_nonneg _))
  have hweight_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.le
  have hweight : s ^ (1 - α) ≤ t ^ (1 - α) :=
    Real.rpow_le_rpow hs.le hst hweight_nonneg
  have hprod := mul_le_mul hweight hmean_bound
    (Real.sqrt_nonneg _) (Real.rpow_nonneg ht.le _)
  have hdyadic_n :
      t ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z t)
            (fun x => vecNormSq (F x))) ≤ K := by
    simpa [t] using hdyadic n
  calc
    s ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z s)
          (fun x => vecNormSq (F x))) ≤
      t ^ (1 - α) *
        ((2 : ℝ) ^ ((d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall z t)
            (fun x => vecNormSq (F x)))) := hprod
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) *
        (t ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z t)
            (fun x => vecNormSq (F x)))) := by ring
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * K :=
      mul_le_mul_of_nonneg_left hdyadic_n
        (Real.rpow_nonneg (by norm_num) _)

end

end PDE
