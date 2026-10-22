module

public import PDEFoundation.Sobolev.Inequalities.SobolevPoincare
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Smooth whole-space Sobolev inequality on the native carrier

This module specializes Mathlib's Gagliardo--Nirenberg--Sobolev inequality to
compactly supported scalar functions on `Vec d`.  The native carrier retains
its inherited supremum norm; the Fréchet derivative is therefore first
estimated by the sum of its coordinate values.  The conversion to the
explicit Euclidean gradient used by the public PDE API is made separately.

No public declaration here uses Mathlib's alternative Euclidean ambient type.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- The critical exponent `2d / (d - 2)` as a nonnegative real. -/
noncomputable def sobolevTwoStar (d : ℕ) : ℝ≥0 :=
  (2 * d) / (d - 2)

/-- The finite-dimensional rank of the native coordinate carrier. -/
theorem finrank_vec (d : ℕ) : Module.finrank ℝ (Vec d) = d := by
  simp [Vec]

/-- The critical exponent has the reciprocal relation required by Mathlib's
whole-space Gagliardo--Nirenberg--Sobolev theorem. -/
theorem inv_sobolevTwoStar
    {d : ℕ} (hd : 3 ≤ d) :
    ((sobolevTwoStar d : ℝ≥0) : ℝ)⁻¹ =
      (2 : ℝ≥0)⁻¹ - (d : ℝ)⁻¹ := by
  have hdle : (2 : ℝ≥0) ≤ (d : ℝ≥0) := by
    exact_mod_cast (by omega : 2 ≤ d)
  rw [sobolevTwoStar, NNReal.coe_inv, NNReal.coe_div,
    NNReal.coe_sub hdle]
  push_cast
  field_simp

/-- The critical exponent agrees with the real-valued public Sobolev
conjugate at `p = 2`. -/
theorem sobolevTwoStar_coe_eq_ofReal_sobolevConjugate_two
    {d : ℕ} (hd : 3 ≤ d) :
    (sobolevTwoStar d : ℝ≥0∞) =
      ENNReal.ofReal (sobolevConjugate d 2) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  have hdle : (2 : ℝ≥0) ≤ (d : ℝ≥0) := by
    exact_mod_cast (by omega : 2 ≤ d)
  rw [sobolevTwoStar, sobolevConjugate, NNReal.coe_div,
    NNReal.coe_sub hdle]
  push_cast
  field_simp

/-- The native smooth compact-support Gagliardo--Nirenberg--Sobolev estimate
at exponent `2`.  Its constant is fixed after the dimension and before the
function or its support. -/
theorem eLpNorm_sobolevTwoStar_le_eLpNorm_fderiv
    {d : ℕ} (hd : 3 ≤ d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) :
    eLpNorm f (sobolevTwoStar d) (volume : Measure (Vec d)) ≤
      eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure (Vec d)) (2 : ℝ≥0) *
        eLpNorm (fderiv ℝ f) 2 (volume : Measure (Vec d)) := by
  have hfinrank : Module.finrank ℝ (Vec d) = d :=
    finrank_vec d
  refine eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume hf hcompact
    (p := 2) (p' := sobolevTwoStar d) (by norm_num) ?_ ?_
  · rw [hfinrank]
    omega
  · rw [hfinrank]
    exact inv_sobolevTwoStar hd

/-- The operator norm of a scalar derivative on native `Vec d` is bounded by
the sum of its coordinate derivatives. -/
theorem norm_clm_le_sum_basisVec
    {d : ℕ} (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin d, ‖L (basisVec i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) ?_
  intro x
  have hx :
      L x = ∑ i : Fin d, x i * L (basisVec i) := by
    calc
      L x = ∑ i : Fin d, x i • L (fun j => if i = j then 1 else 0) := by
        simpa using (LinearMap.pi_apply_eq_sum_univ (f := L.toLinearMap) x)
      _ = ∑ i : Fin d, x i • L (basisVec i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        have hbasis : (fun j => if i = j then 1 else 0) = basisVec i := by
          funext j
          simp [basisVec_apply, eq_comm]
        rw [hbasis]
      _ = ∑ i : Fin d, x i * L (basisVec i) := by
        simp only [smul_eq_mul]
  calc
    ‖L x‖ = ‖∑ i : Fin d, x i * L (basisVec i)‖ := by rw [hx]
    _ ≤ ∑ i : Fin d, ‖x i * L (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, ‖x i‖ * ‖L (basisVec i)‖ := by
      simp only [norm_mul]
    _ ≤ ∑ i : Fin d, ‖x‖ * ‖L (basisVec i)‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_right
        (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin d, ‖L (basisVec i)‖) * ‖x‖ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Finset.mul_sum (s := Finset.univ)
          (f := fun i : Fin d => ‖L (basisVec i)‖) ‖x‖).symm

/-- Coordinate form of the native smooth compact-support Sobolev estimate. -/
theorem eLpNorm_sobolevTwoStar_le_sum_eLpNorm_fderiv_apply_basisVec
    {d : ℕ} (hd : 3 ≤ d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) :
    eLpNorm f (sobolevTwoStar d) (volume : Measure (Vec d)) ≤
      eLpNormLESNormFDerivOfEqInnerConst
          (volume : Measure (Vec d)) (2 : ℝ≥0) *
        ∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) 2
            (volume : Measure (Vec d)) := by
  refine (eLpNorm_sobolevTwoStar_le_eLpNorm_fderiv hd hf hcompact).trans ?_
  refine mul_le_mul_right ?_ _
  have hcontinuous : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv one_ne_zero
  calc
    eLpNorm (fderiv ℝ f) 2 (volume : Measure (Vec d)) ≤
        eLpNorm (fun x => ∑ i : Fin d,
          ‖(fderiv ℝ f x) (basisVec i)‖) 2 volume := by
      apply eLpNorm_mono hcontinuous.aestronglyMeasurable
      intro x
      exact (norm_clm_le_sum_basisVec (fderiv ℝ f x)).trans_eq <| by
        rw [Real.norm_of_nonneg]
        exact Finset.sum_nonneg fun i _ => norm_nonneg _
    _ ≤ ∑ i : Fin d,
        eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) 2 volume := by
      rw [← Finset.sum_fn]
      exact eLpNorm_sum_le (by norm_num)
    _ = ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) 2 volume := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact eLpNorm_norm _
        (hcontinuous.clm_apply continuous_const).aestronglyMeasurable

end PDE
