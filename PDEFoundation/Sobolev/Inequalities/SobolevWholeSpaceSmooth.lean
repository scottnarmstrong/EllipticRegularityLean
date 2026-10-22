module

public import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolevSmooth

/-!
# Smooth whole-space Sobolev inequality for `1 ≤ p < d`

Mathlib's Gagliardo--Nirenberg--Sobolev theorem for compactly supported `C¹`
functions, specialized to the native carrier `Vec d`.  The constant produced by
Mathlib factors as `C₁(d) * p (d - 1) / (d - p)` with `C₁(d)` independent of
`p`, which is exactly the shape required by the public Sobolev proposition.
The native Fréchet derivative uses the supremum norm, so it is bounded by the
sum of its coordinates.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- The exponent-independent constant of Mathlib's `L¹` Gagliardo--Nirenberg
inequality on `Vec d`. -/
noncomputable def sobolevOneConstant (d : ℕ) : ℝ≥0 :=
  eLpNormLESNormFDerivOneConst (volume : Measure (Vec d)) (NNReal.conjExponent d)

/-- The operator norm of the native derivative is bounded by the `p`-norm sum
of its coordinate derivatives. -/
theorem eLpNorm_fderiv_le_sum_eLpNorm_fderiv_apply_basisVec
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    eLpNorm (fderiv ℝ f) p (volume : Measure (Vec d)) ≤
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) p
          (volume : Measure (Vec d)) := by
  have hcontinuous : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv one_ne_zero
  calc
    eLpNorm (fderiv ℝ f) p (volume : Measure (Vec d)) ≤
        eLpNorm (fun x => ∑ i : Fin d,
          ‖(fderiv ℝ f x) (basisVec i)‖) p volume := by
      apply eLpNorm_mono hcontinuous.aestronglyMeasurable
      intro x
      exact (norm_clm_le_sum_basisVec (fderiv ℝ f x)).trans_eq <| by
        rw [Real.norm_of_nonneg]
        exact Finset.sum_nonneg fun i _ => norm_nonneg _
    _ ≤ ∑ i : Fin d,
        eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) p volume := by
      rw [← Finset.sum_fn]
      exact eLpNorm_sum_le hp
    _ = ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) p volume := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact eLpNorm_norm _
        (hcontinuous.clm_apply continuous_const).aestronglyMeasurable

/-- The smooth compact-support Sobolev inequality for `1 ≤ p < d`, in coordinate
form.  The constant is `sobolevOneConstant d` times `p (d - 1) / (d - p)`. -/
theorem eLpNorm_sobolevConjugate_le_sum_eLpNorm_fderiv_apply_basisVec
    {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 1 ≤ p) (hpd : p < d)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f) :
    eLpNorm f (ENNReal.ofReal (sobolevConjugate d p)) (volume : Measure (Vec d)) ≤
      ENNReal.ofReal
          ((sobolevOneConstant d : ℝ) * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
        ∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) (ENNReal.ofReal p)
            (volume : Measure (Vec d)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hq : 0 < sobolevConjugate d p := sobolevConjugate_pos hp0 hpd
  have hfinrank : Module.finrank ℝ (Vec d) = d := finrank_vec d
  have hmain :=
    eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure (Vec d)) hf hcompact
      (p := p.toNNReal) (p' := (sobolevConjugate d p).toNNReal)
      (by rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hp)
      (by rw [hfinrank]; omega)
      (by
        rw [hfinrank, Real.coe_toNNReal _ hq.le, NNReal.coe_inv,
          Real.coe_toNNReal _ hp0.le]
        exact inv_sobolevConjugate hp0 hpd)
  have hpcoe : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p := rfl
  have hqcoe :
      (((sobolevConjugate d p).toNNReal : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (sobolevConjugate d p) := rfl
  rw [hpcoe, hqcoe] at hmain
  refine hmain.trans ?_
  have hconst :
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Vec d))
          p.toNNReal : ℝ≥0∞) =
        ENNReal.ofReal
          ((sobolevOneConstant d : ℝ) * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) := by
    have hpos : 0 ≤ p * ((d : ℝ) - 1) / ((d : ℝ) - p) := by
      have : (0 : ℝ) < (d : ℝ) - p := sub_pos.mpr hpd
      have : (0 : ℝ) ≤ (d : ℝ) - 1 := by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      positivity
    simp only [eLpNormLESNormFDerivOfEqInnerConst, sobolevOneConstant, hfinrank]
    rw [ENNReal.coe_mul, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hp0.le]
    rfl
  rw [hconst]
  exact mul_le_mul_right
    (eLpNorm_fderiv_le_sum_eLpNorm_fderiv_apply_basisVec
      (by exact_mod_cast ENNReal.one_le_ofReal.mpr hp) hf) _

end PDE
