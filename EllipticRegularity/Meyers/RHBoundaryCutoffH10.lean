module

public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff

/-!
# Smooth compactly supported multipliers of `H¹₀`

For `u ∈ H¹₀(U)` and a smooth compactly supported multiplier `η`, with no
condition on the support of `η` relative to `U`, the product `η u` is again in
`H¹₀(U)`: multiply the smooth compactly supported approximants of `u` by `η`.
This is the step "`η u ∈ H¹₀(B₁)` since `u` has zero trace" of the boundary
case of the reverse Hölder lemma.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PDE

namespace MeyersRH

variable {d : ℕ} {U : Set (Vec d)}

theorem exists_h10_mul_contDiff (u : H10Function U) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∃ v : H10Function U, v.toFun = fun x => η x * u.toFun x := by
  obtain ⟨M, hM⟩ := hηc.exists_bound_of_continuous hη.continuous
  have hDηc : ∀ i : Fin d, HasCompactSupport (fun x => fderiv ℝ η x (basisVec i)) := fun i =>
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hDηcont : ∀ i : Fin d, Continuous (fun x => fderiv ℝ η x (basisVec i)) := fun i =>
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hM' : ∀ i : Fin d, ∃ M' : ℝ, ∀ x, ‖fderiv ℝ η x (basisVec i)‖ ≤ M' := fun i =>
    (hDηc i).exists_bound_of_continuous (hDηcont i)
  choose M' hM' using hM'
  let w : H1Function U := u.toH1Function.mulContDiffHasCompactSupport hη hηc
  have hwfun : w.toFun = fun x => η x * u.toFun x := by
    simp [w]
  have hwgrad : ∀ i x, w.grad x i = η x * u.grad x i + u.toFun x * fderiv ℝ η x (basisVec i) := by
    intro i x
    simp [w, classicalGradient_apply]
  refine ⟨{ toH1Function := w
            approx := fun n x => η x * u.approx n x
            approx_smooth := fun n => hη.mul (u.approx_smooth n)
            approx_hasCompactSupport := fun n => (u.approx_hasCompactSupport n).mul_left
            approx_support_subset := fun n =>
              tsupport_mul_subset_right.trans (u.approx_support_subset n)
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, hwfun⟩
  · -- values
    have hconv := u.tendsto_approx
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M) hconv (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    have hmeas : AEStronglyMeasurable
        (fun x => η x * u.approx n x - w.toFun x) (volume.restrict U) := by
      rw [hwfun]
      exact (hη.continuous.mul (u.approx_smooth n).continuous).aestronglyMeasurable.sub
        (hη.continuous.aestronglyMeasurable.mul u.toH1Function.memL2.aestronglyMeasurable)
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas (Eventually.of_forall fun x => ?_) _
    rw [hwfun]
    have : η x * u.approx n x - η x * u.toFun x = η x * (u.approx n x - u.toFun x) := by ring
    simp only [this, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  · intro i
    have hA := u.tendsto_approx_grad i
    have hB := u.tendsto_approx
    have h := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M) hA (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (M' i)) hB (Or.inr ENNReal.ofReal_ne_top))
    rw [mul_zero, mul_zero, add_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    have hameas : AEStronglyMeasurable
        (fun x => fderiv ℝ (fun y => η y * u.approx n y) x (basisVec i) * 0 +
          (fderiv ℝ (u.approx n) x (basisVec i) - u.toH1Function.grad x i)) (volume.restrict U) := by
      simp only [mul_zero, zero_add]
      exact ((((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable).sub
        ((u.toH1Function.gradMemL2 i).aestronglyMeasurable)
    have hbmeas : AEStronglyMeasurable
        (fun x => u.approx n x - u.toH1Function.toFun x) (volume.restrict U) :=
      (u.approx_smooth n).continuous.aestronglyMeasurable.sub
        u.toH1Function.memL2.aestronglyMeasurable
    have hameas' : AEStronglyMeasurable
        (fun x => fderiv ℝ (u.approx n) x (basisVec i) - u.toH1Function.grad x i)
        (volume.restrict U) := by
      simpa using hameas
    have hf1 : AEStronglyMeasurable (fun x => η x *
        (fderiv ℝ (u.approx n) x (basisVec i) - u.toH1Function.grad x i)) (volume.restrict U) :=
      hη.continuous.aestronglyMeasurable.mul hameas'
    have hf2 : AEStronglyMeasurable (fun x => fderiv ℝ η x (basisVec i) *
        (u.approx n x - u.toH1Function.toFun x)) (volume.restrict U) :=
      (hDηcont i).aestronglyMeasurable.mul hbmeas
    have hid : (fun x => fderiv ℝ (fun y => η y * u.approx n y) x (basisVec i) -
          w.grad x i) =
        (fun x => η x * (fderiv ℝ (u.approx n) x (basisVec i) - u.toH1Function.grad x i)) +
          (fun x => fderiv ℝ η x (basisVec i) * (u.approx n x - u.toH1Function.toFun x)) := by
      funext x
      rw [fderiv_fun_mul (hη.differentiable (by simp) x)
        (((u.approx_smooth n).differentiable (by simp)) x), hwgrad]
      simp only [add_apply, smul_apply, smul_eq_mul,
        Pi.add_apply]
      ring
    rw [hid]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf1
        (Eventually.of_forall fun x => by
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)) _
    · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf2
        (Eventually.of_forall fun x => by
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_right (hM' i x) (norm_nonneg _)) _

end MeyersRH

end PDE
