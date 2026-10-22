module

public import EllipticRegularity.Holder.PlanarOscillationDecay

/-! # Sharp-order planar oscillation exponent -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The planar oscillation exponent is bounded below by a numerical multiple
of `Λ⁻¹ᐟ²`; this is the sharp ellipticity order. -/
theorem planar_oscillation_exponent_lowerBound
    {Lam : ℝ} {a : CoeffField 2}
    (x : Vec 2) (hx : x ∈ euclideanBall (0 : Vec 2) (3 / 4))
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a) :
    Real.sqrt (1 / Lam) / (4 * 687865857) ≤
      holeFillingDyadicExponent (687865857 * Real.sqrt Lam) / 2 := by
  have hroot := centeredAxisCube_one_thirtysecond_subset_unit x hx
  have h := square_hole_filling_dyadicExponent_lowerBound
    x (by norm_num : (0 : ℝ) < 1 / 32) hroot hEll
  norm_num only [div_one] at h
  nlinarith [h]

private theorem planar_alpha_le_half_exponent
    {Lam C : ℝ} (hLam : 0 < Lam)
    (hC : (4 * 687865857 : ℝ) ^ 2 ≤ C) :
    (C * Lam) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt (1 / Lam) / (4 * 687865857) := by
  let D : ℝ := 4 * 687865857
  have hD : 0 < D := by norm_num [D]
  have hCpos : 0 < C := lt_of_lt_of_le (sq_pos_of_pos hD) hC
  have hCroot : D ≤ Real.sqrt C := by
    have hsq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hCpos.le
    nlinarith [Real.sqrt_nonneg C]
  have hden : D * Real.sqrt Lam ≤ Real.sqrt C * Real.sqrt Lam :=
    mul_le_mul_of_nonneg_right hCroot (Real.sqrt_nonneg Lam)
  have hdenpos : 0 < D * Real.sqrt Lam := mul_pos hD (Real.sqrt_pos.mpr hLam)
  have hbound : 1 / (Real.sqrt C * Real.sqrt Lam) ≤
      1 / (D * Real.sqrt Lam) :=
    div_le_div_of_nonneg_left (by norm_num) hdenpos hden
  have hsqrtprod : Real.sqrt (C * Lam) = Real.sqrt C * Real.sqrt Lam :=
    Real.sqrt_mul hCpos.le Lam
  have hsqrtinv : Real.sqrt (1 / Lam) = 1 / Real.sqrt Lam := by
    rw [one_div, Real.sqrt_inv, one_div]
  calc
    (C * Lam) ^ (-(1 / 2 : ℝ)) =
        1 / (Real.sqrt C * Real.sqrt Lam) := by
      rw [Real.rpow_neg (mul_nonneg hCpos.le hLam.le),
        ← Real.sqrt_eq_rpow, hsqrtprod]
      ring
    _ ≤ 1 / (D * Real.sqrt Lam) := hbound
    _ = Real.sqrt (1 / Lam) / D := by
      rw [hsqrtinv]
      field_simp [hD.ne', (Real.sqrt_pos.mpr hLam).ne']

/-- Every exponent `(C Λ)⁻¹ᐟ²` with the displayed numerical threshold is
admissible in the planar oscillation estimate. -/
theorem planar_essentialOscillationLEOn_decay_with_alpha
    {Lam C : ℝ} {a : CoeffField 2}
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    (x : Vec 2) (hx : x ∈ euclideanBall (0 : Vec 2) (3 / 4))
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec 2) 1) u)
    (hC : (4 * 687865857 : ℝ) ^ 2 ≤ C)
    {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 64) :
    HasEssentialOscillationLEOn u.toFun (centeredAxisCube x s)
      (131072 * Real.sqrt Lam * (s ^ ((C * Lam) ^ (-(1 / 2 : ℝ)))) *
        Real.sqrt (∫ z in euclideanBall (0 : Vec 2) 1, (u z) ^ 2)) := by
  have hLam : 0 < Lam :=
    (hEll.elliptic (centeredAxisCube_one_thirtysecond_subset_unit x hx
      (center_mem_centeredAxisCube x (by norm_num)))).Lam_pos
  have hα : (C * Lam) ^ (-(1 / 2 : ℝ)) ≤
      holeFillingDyadicExponent (687865857 * Real.sqrt Lam) / 2 :=
    (planar_alpha_le_half_exponent hLam hC).trans
      (planar_oscillation_exponent_lowerBound x hx hEll)
  have hpow : s ^ (holeFillingDyadicExponent
      (687865857 * Real.sqrt Lam) / 2) ≤
      s ^ ((C * Lam) ^ (-(1 / 2 : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hs (by linarith) hα
  obtain ⟨lo, hi, hrange, hwidth⟩ :=
    planar_essentialOscillationLEOn_decay x hx hEll hsol hs hsmax
  refine ⟨lo, hi, hrange, hwidth.trans ?_⟩
  have hcoeff : 0 ≤ 131072 * Real.sqrt Lam :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hL : 0 ≤ Real.sqrt
      (∫ z in euclideanBall (0 : Vec 2) 1, (u z) ^ 2) :=
    Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hcoeff) hL

end

end PDE
