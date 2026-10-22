module

public import PDEFoundation.PDE.HarmonicMeanValueLocal
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.FiniteVectorAverageJensen
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Local `L∞` control of smooth harmonic functions by their ball `L²` mean -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem abs_integralAverage_le_sqrt_integralAverage_sq
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volumeOn U))
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    |integralAverage U f| ≤
      Real.sqrt (integralAverage U (fun x => f x ^ 2)) := by
  let g : Vec d → Vec 1 := fun x => fun _ => f x
  have hg : ∀ i : Fin 1, MemLp (fun x => g x i) 2 (volumeOn U) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hf
  have hJ := vecEuclideanNorm_coordinateVectorAverage_sub_le_sqrt_integralAverage
    hg hUpos hUtop (0 : Vec 1)
  have hmean : coordinateVectorAverage U g =
      scalarToVecOne (integralAverage U f) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [hmean, sub_zero] at hJ
  have hnorm : vecEuclideanNorm (scalarToVecOne (integralAverage U f)) =
      |integralAverage U f| := by
    simp [vecEuclideanNorm, vecNormSq, vecDot, scalarToVecOne]
    rw [show (integralAverage U f) * integralAverage U f =
      (integralAverage U f) ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hsq : (fun x => vecNormSq (g x - 0)) = fun x => f x ^ 2 := by
    funext x
    simp [g, vecNormSq, vecDot, pow_two]
  rw [hnorm] at hJ
  calc
    |integralAverage U f| ≤
        Real.sqrt (integralAverage U (fun x => vecNormSq (g x - 0))) := hJ
    _ = Real.sqrt (integralAverage U (fun x => f x ^ 2)) := by rw [hsq]

private theorem integralAverage_sq_mono_ball
    {d : ℕ} {x₀ y : Vec d} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ euclideanClosedBall x₀ (r / 2))
    {f : Vec d → ℝ} (hf : IntegrableOn f (euclideanBall x₀ r))
    (hfnonneg : ∀ z, 0 ≤ f z) :
    integralAverage (euclideanBall y (r / 4)) f ≤
      4 ^ d * integralAverage (euclideanBall x₀ r) f := by
  have hyNorm : vecEuclideanNorm (y - x₀) ≤ r / 2 := by
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mp hy
  have hsubset : euclideanBall y (r / 4) ⊆ euclideanBall x₀ r := by
    apply euclideanBall_subset_of_center_norm_add_le (by positivity) hr
    have hbound : vecEuclideanNorm (y - x₀) + r / 4 ≤ r := by
      nlinarith [hyNorm, hr]
    exact hbound
  have hIntLe :
      (∫ z in euclideanBall y (r / 4), f z ∂volume) ≤
        ∫ z in euclideanBall x₀ r, f z ∂volume := by
    apply setIntegral_mono_set hf
      (ae_of_all (volume.restrict (euclideanBall x₀ r)) hfnonneg)
    exact ae_of_all volume fun z hz => hsubset hz
  have hSmallPos := volume_euclideanBall_toReal_pos y (show 0 < r / 4 by positivity)
  have hBigPos := volume_euclideanBall_toReal_pos x₀ hr
  have hRatio :
      (volume (euclideanBall x₀ r)).toReal /
        (volume (euclideanBall y (r / 4))).toReal = 4 ^ d := by
    rw [volume_euclideanBall_toReal_div_eq_div_pow x₀ y
      (show 0 < r / 4 by positivity) hr]
    have hrad : r / (r / 4) = 4 := by field_simp
    rw [hrad]
  have hSmallEq :
      (volume (euclideanBall x₀ r)).toReal / (4 : ℝ) ^ d =
        (volume (euclideanBall y (r / 4))).toReal := by
    have hmul := (div_eq_iff hSmallPos.ne').mp hRatio
    rw [hmul]
    field_simp [pow_ne_zero d (by norm_num : (4 : ℝ) ≠ 0)]
  have hCoeff :
      (volume (euclideanBall y (r / 4))).toReal⁻¹ =
        4 ^ d * (volume (euclideanBall x₀ r)).toReal⁻¹ := by
    rw [← hSmallEq]
    field_simp [hBigPos.ne', pow_ne_zero d (by norm_num : (4 : ℝ) ≠ 0)]
  unfold integralAverage
  rw [hCoeff]
  have hnormInt := mul_le_mul_of_nonneg_left hIntLe
    (inv_nonneg.mpr hBigPos.le)
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hnormInt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) d))

/-- Interior pointwise control of a smooth harmonic function by its normalized
quadratic mean.  The volume ratio from the radius `r / 4` ball to the outer
radius `r` ball gives the sharp dimensional factor `2 ^ d`. -/
theorem abs_harmonic_le_pow_mul_sqrt_integralAverage_sq
    (hd : 0 < d) {v : Vec d → ℝ} {x₀ y : Vec d} {r : ℝ}
    (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x₀ r))
    (hharm : ∀ z ∈ euclideanBall x₀ r,
      euclideanCoordLaplacian v z = 0)
    (hL2 : IntegrableOn (fun z => v z ^ 2) (euclideanBall x₀ r))
    (hy : y ∈ euclideanClosedBall x₀ (r / 2)) :
    |v y| ≤ (2 : ℝ) ^ d *
      Real.sqrt (integralAverage (euclideanBall x₀ r)
        (fun z => v z ^ 2)) := by
  have hyNorm : vecEuclideanNorm (y - x₀) ≤ r / 2 := by
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mp hy
  have hOuter : euclideanBall y (r / 2) ⊆ euclideanBall x₀ r := by
    apply euclideanBall_subset_of_center_norm_add_le (by positivity) hr
    have hbound : vecEuclideanNorm (y - x₀) + r / 2 ≤ r := by
      nlinarith [hyNorm, hr]
    exact hbound
  have hvOuter : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall y (r / 2)) :=
    hv.mono hOuter
  have hharmOuter : ∀ z ∈ euclideanBall y (r / 2),
      euclideanCoordLaplacian v z = 0 := by
    intro z hz
    exact hharm z (hOuter hz)
  have hmean := integralAverage_euclideanBall_eq_center_of_harmonicOn
    (d := d) (x := y) (R := r / 2) (s := r / 4)
    hd hvOuter hharmOuter (by positivity) (by linarith [hr])
  let U := euclideanBall y (r / 4)
  have hUinner : U ⊆ euclideanBall y (r / 2) := by
    dsimp [U]
    exact euclideanBall_mono (by positivity) (by linarith [hr])
  have hUouter : U ⊆ euclideanBall x₀ r := hUinner.trans hOuter
  have hsmallInt : IntegrableOn (fun z => v z ^ 2) U := hL2.mono_set hUouter
  have hUmeas : AEStronglyMeasurable v (volumeOn U) := by
    have hcont : ContinuousOn v U := hvOuter.continuousOn.mono hUinner
    exact hcont.aestronglyMeasurable (isOpen_euclideanBall y (r / 4)).measurableSet
  have hMemLp : MemLp v 2 (volumeOn U) :=
    (memLp_two_iff_integrable_sq hUmeas).2 hsmallInt
  have hUpos : 0 < volume U := by
    dsimp [U]
    exact volume_euclideanBall_pos y (by positivity)
  have hUtop : volume U < ∞ := by
    dsimp [U]
    exact (volume_euclideanBall_ne_top y (by positivity)).lt_top
  have hCS := abs_integralAverage_le_sqrt_integralAverage_sq
    hMemLp hUpos hUtop
  have hpoint : |v y| ≤
      Real.sqrt (integralAverage U (fun z => v z ^ 2)) := by
    rw [← hmean]
    exact hCS
  have hcompare := integralAverage_sq_mono_ball hr hy hL2
    (fun z => sq_nonneg (v z))
  have hfactor : Real.sqrt ((4 : ℝ) ^ d) = (2 : ℝ) ^ d := by
    have hpow : (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 := by
      calc
        (4 : ℝ) ^ d = ((2 : ℝ) ^ 2) ^ d := by norm_num
        _ = (2 : ℝ) ^ (2 * d) := by rw [← pow_mul]
        _ = (2 : ℝ) ^ (d * 2) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ d) ^ 2 := by rw [pow_mul]
    rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg (by norm_num) d)]
  calc
    |v y| ≤ Real.sqrt (integralAverage U (fun z => v z ^ 2)) := hpoint
    _ ≤ Real.sqrt (4 ^ d * integralAverage (euclideanBall x₀ r)
          (fun z => v z ^ 2)) := Real.sqrt_le_sqrt hcompare
    _ = (2 : ℝ) ^ d * Real.sqrt (integralAverage (euclideanBall x₀ r)
          (fun z => v z ^ 2)) := by
      rw [Real.sqrt_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) d), hfactor]

end

end PDE
