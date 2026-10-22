module

public import PDEFoundation.Analysis.Newtonian.Representation.Regularized

/-!
# Calculus of the regularized Newton kernel

Directional derivatives of the regularized kernel and of its potential `regPotential ε`,
with `∇ regPotential ε = regKernel ε` and `div regKernel ε = regDiv ε`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE

namespace NewtonRepresentation

noncomputable section

variable {d : ℕ} {ε : ℝ}

theorem hasFDerivAt_vecNormSq (z : Vec d) :
    HasFDerivAt (vecNormSq : Vec d → ℝ)
      (∑ i : Fin d, (2 * z i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z := by
  have : (vecNormSq : Vec d → ℝ) = fun z => ∑ i : Fin d, z i ^ 2 := funext vecNormSq_eq_sum_sq
  rw [this]
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have hp : HasFDerivAt (fun y : Vec d => y i) (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) z :=
    (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).hasFDerivAt
  have h := hp.mul hp
  have e : (fun y : Vec d => y i ^ 2) = fun y => y i * y i := funext fun y => pow_two _
  rw [e]
  convert h using 1
  rw [← two_smul ℝ, smul_smul]

theorem fderiv_vecNormSq_apply (z v : Vec d) : fderiv ℝ vecNormSq z v = 2 * vecDot z v := by
  rw [(hasFDerivAt_vecNormSq z).fderiv]
  simp [vecDot, Finset.mul_sum, mul_assoc]

/-- The second scalar factor, `regCoef` with the exponent lowered by one. -/
def regCoef2 (d : ℕ) (ε : ℝ) (z : Vec d) : ℝ :=
  newtonConst d * (vecNormSq z + ε ^ 2) ^ (-((d : ℝ) / 2) - 1)

theorem regCoef_eq_mul (hε : ε ≠ 0) (z : Vec d) :
    regCoef d ε z = regCoef2 d ε z * (vecNormSq z + ε ^ 2) := by
  have : 0 < vecNormSq z + ε ^ 2 := by have := vecNormSq_nonneg z; positivity
  unfold regCoef regCoef2
  rw [mul_assoc, ← Real.rpow_add_one this.ne']
  congr 2
  ring

theorem hasFDerivAt_regCoef (hε : ε ≠ 0) (z : Vec d) :
    HasFDerivAt (regCoef d ε)
      ((newtonConst d * (-((d : ℝ) / 2) * (vecNormSq z + ε ^ 2) ^ (-((d : ℝ) / 2) - 1))) •
        ∑ i : Fin d, (2 * z i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z := by
  have hs : 0 < vecNormSq z + ε ^ 2 := by have := vecNormSq_nonneg z; positivity
  have h1 : HasFDerivAt (fun y : Vec d => vecNormSq y + ε ^ 2)
      (∑ i : Fin d, (2 * z i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z :=
    (hasFDerivAt_vecNormSq z).add_const _
  have h2 := (h1.rpow_const (p := -((d : ℝ) / 2)) (Or.inl hs.ne')).const_mul (newtonConst d)
  unfold regCoef
  refine h2.congr_fderiv ?_
  rw [smul_smul]

theorem fderiv_regCoef_apply (hε : ε ≠ 0) (z v : Vec d) :
    fderiv ℝ (regCoef d ε) z v = -((d : ℝ) * regCoef2 d ε z * vecDot z v) := by
  rw [(hasFDerivAt_regCoef hε z).fderiv]
  simp [regCoef2, vecDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hasFDerivAt_regKernel_apply (hε : ε ≠ 0) (z : Vec d) (i : Fin d) :
    HasFDerivAt (fun y : Vec d => regKernel ε y i)
      (z i • fderiv ℝ (regCoef d ε) z +
        regCoef d ε z • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z := by
  have hp : HasFDerivAt (fun y : Vec d => y i) (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) z :=
    (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).hasFDerivAt
  have hc : HasFDerivAt (regCoef d ε) (fderiv ℝ (regCoef d ε) z) z :=
    (hasFDerivAt_regCoef hε z).differentiableAt.hasFDerivAt
  have h := hc.mul hp
  have e : (fun y : Vec d => regKernel ε y i) = fun y => regCoef d ε y * y i := by
    funext y; simp [regKernel]
  rw [e]
  convert h using 1
  rw [add_comm]

theorem fderiv_regKernel_apply_basis (hε : ε ≠ 0) (z : Vec d) (i : Fin d) :
    fderiv ℝ (fun y : Vec d => regKernel ε y i) z (basisVec i) =
      regCoef d ε z - (d : ℝ) * regCoef2 d ε z * z i ^ 2 := by
  rw [(hasFDerivAt_regKernel_apply hε z i).fderiv]
  simp [fderiv_regCoef_apply hε, vecDot_basisVec_right]
  ring

/-- The divergence of the regularized kernel (an approximate identity). -/
def regDiv (d : ℕ) (ε : ℝ) (z : Vec d) : ℝ :=
  (d : ℝ) * ε ^ 2 * regCoef2 d ε z

theorem sum_fderiv_regKernel (hε : ε ≠ 0) (z : Vec d) :
    ∑ i : Fin d, fderiv ℝ (fun y : Vec d => regKernel ε y i) z (basisVec i) = regDiv d ε z := by
  simp only [fderiv_regKernel_apply_basis hε, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [regCoef_eq_mul hε z, ← vecNormSq_eq_sum_sq]
  unfold regDiv
  ring

theorem contDiff_regKernel_apply (hε : ε ≠ 0) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => regKernel ε y i) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (vecNormSq : Vec d → ℝ) := contDiff_vecNormSq
  have hpos : ∀ y : Vec d, vecNormSq y + ε ^ 2 ≠ 0 := fun y => by
    have := vecNormSq_nonneg y; positivity
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => regCoef d ε y) := by
    unfold regCoef
    exact contDiff_const.mul ((hq.add contDiff_const).rpow_const_of_ne hpos)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y i) := by fun_prop
  simpa [regKernel] using h1.mul h2

/-- The radial primitive `G` with `G' t = (newtonConst d / 2) t^(-d/2)`. -/
def regG (d : ℕ) (t : ℝ) : ℝ :=
  newtonConst d / 2 *
    (if d = 2 then Real.log t else t ^ (1 - (d : ℝ) / 2) / (1 - (d : ℝ) / 2))

theorem hasDerivAt_regG {t : ℝ} (ht : 0 < t) :
    HasDerivAt (regG d) (newtonConst d / 2 * t ^ (-((d : ℝ) / 2))) t := by
  unfold regG
  refine HasDerivAt.const_mul _ ?_
  by_cases h2 : d = 2
  · subst h2
    simp only [ite_true, Nat.cast_ofNat]
    have := Real.hasDerivAt_log ht.ne'
    convert this using 1
    rw [show -((2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  · simp only [h2, ite_false]
    have hne : (1 - (d : ℝ) / 2) ≠ 0 := by
      intro h
      apply h2
      have : (d : ℝ) = 2 := by linarith
      exact_mod_cast this
    have := (Real.hasDerivAt_rpow_const (x := t) (p := 1 - (d : ℝ) / 2) (Or.inl ht.ne')).div_const
      (1 - (d : ℝ) / 2)
    convert this using 1
    rw [mul_div_cancel_left₀ _ hne]
    congr 1
    ring

/-- The potential of the regularized kernel: `∇ regPotential ε = regKernel ε`. -/
def regPotential (d : ℕ) (ε : ℝ) (z : Vec d) : ℝ :=
  regG d (vecNormSq z + ε ^ 2)

theorem hasFDerivAt_regPotential (hε : ε ≠ 0) (z : Vec d) :
    HasFDerivAt (regPotential d ε)
      (∑ i : Fin d, regKernel ε z i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z := by
  have hs : 0 < vecNormSq z + ε ^ 2 := by have := vecNormSq_nonneg z; positivity
  have h1 : HasFDerivAt (fun y : Vec d => vecNormSq y + ε ^ 2)
      (∑ i : Fin d, (2 * z i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) z :=
    (hasFDerivAt_vecNormSq z).add_const _
  have h2 := (hasDerivAt_regG (d := d) hs).comp_hasFDerivAt z h1
  unfold regPotential
  refine h2.congr_fderiv ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  simp only [regKernel, regCoef, Pi.smul_apply, smul_eq_mul]
  ring

theorem fderiv_regPotential_apply (hε : ε ≠ 0) (z v : Vec d) :
    fderiv ℝ (regPotential d ε) z v = vecDot (regKernel ε z) v := by
  rw [(hasFDerivAt_regPotential hε z).fderiv]
  simp [vecDot]

theorem contDiff_one_regPotential (hε : ε ≠ 0) : ContDiff ℝ 1 (regPotential d ε) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun z => ∑ i : Fin d, regKernel ε z i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ),
    ?_, fun z => hasFDerivAt_regPotential hε z⟩
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((contDiff_regKernel_apply hε i).continuous).smul continuous_const

end

end NewtonRepresentation

end PDE
