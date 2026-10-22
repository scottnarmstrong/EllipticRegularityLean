module

public import PDEFoundation.Analysis.Newtonian.Potential.Decay
public import PDEFoundation.Analysis.Newtonian.Potential.KernelLipschitz
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Decay of the gradient of the Newton potential

For `tsupport F ⊆ B_R` and `|x| ≥ 2R`, `|∂_k u_F x| ≤ C |x|^{-d}`.  The proof uses the formula
`∂_k u_F = Σ_i E_i ⋆ ∂_k F_i`, the vanishing `∫ ∂_k F_i = 0`, and the Lipschitz estimate of `E_i`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- A coordinate derivative of a smooth compactly supported function integrates to zero. -/
theorem integral_euclideanCoordDeriv_eq_zero {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (k : Fin d) :
    ∫ y, euclideanCoordDeriv k g y = 0 := by
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hc : Continuous (fun z => fderiv ℝ g z (basisVec k)) := hdc.clm_apply continuous_const
  have hs : HasCompactSupport (fun z => fderiv ℝ g z (basisVec k)) :=
    (hgc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec k)) (by simp)
  have h1 : Integrable (fun z => fderiv ℝ g z (basisVec k)) volume :=
    hc.integrable_of_hasCompactSupport hs
  have h2 : Integrable g volume :=
    hg.continuous.integrable_of_hasCompactSupport hgc
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec d))) (f := fun _ : Vec d => (1 : ℝ)) (g := g)
    (v := basisVec k)
    (by simp) (by simpa using h1) (by simpa using h2)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => (hg.differentiable (by simp)) x)
  simpa [euclideanCoordDeriv] using this

theorem tsupport_apply_subset {F : Vec d → Vec d} (i : Fin d) :
    tsupport (fun z => F z i) ⊆ tsupport F := by
  refine closure_mono fun z hz => ?_
  intro h
  exact hz (by simp [h])

theorem abs_coordDeriv_newtonPotential_le (hd : 0 < d) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport F ⊆ euclideanBall 0 R) (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d, 2 * R ≤ vecEuclideanNorm x →
      |euclideanCoordDeriv k (newtonPotential F) x| ≤ C * vecEuclideanNorm x ^ (-(d : ℝ)) := by
  have hgs : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun z => F z i) :=
    fun i => (contDiff_pi.mp hF) i
  set G : Vec d → Vec d := fun y i => euclideanCoordDeriv k (fun z => F z i) y with hGdef
  have hGc : ∀ i : Fin d, Continuous (fun y => G y i) := fun i =>
    ((hgs i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hGs : ∀ i : Fin d, HasCompactSupport (fun y => G y i) := fun i =>
    ((hasCompactSupport_apply hFc i).fderiv ℝ).comp_left
      (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec k)) (by simp)
  have hGint : ∀ i : Fin d, Integrable (fun y => |G y i|) volume := fun i =>
    ((hGc i).abs).integrable_of_hasCompactSupport ((hGs i).comp_left (g := fun r : ℝ => |r|) (by simp))
  have hG0 : ∀ i : Fin d, ∫ y, G y i = 0 := fun i =>
    integral_euclideanCoordDeriv_eq_zero (hgs i) (hasCompactSupport_apply hFc i) k
  have hGsupp : ∀ y : Vec d, G y ≠ 0 → vecEuclideanNorm y < R := by
    intro y hy
    have hy' : ∃ i, G y i ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (funext h)
    obtain ⟨i, hi⟩ := hy'
    have hmem : y ∈ tsupport (fun z => F z i) :=
      tsupport_euclideanCoordDeriv_subset_tsupport k _ (subset_tsupport _ hi)
    have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp
      (hsupp (tsupport_apply_subset i hmem))
    simpa only [sub_zero] using this
  set S : ℝ := ∑ i : Fin d, ∫ y, |G y i| with hS
  refine ⟨newtonConst d * (1 + 2 * d) * 2 ^ d * R * S, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg newtonConst_nonneg (by positivity))
      (by positivity)) hR.le) (Finset.sum_nonneg fun i _ => integral_nonneg fun y => abs_nonneg _)
  intro x hx
  have hxpos : 0 < vecEuclideanNorm x := by linarith
  set K : ℝ := newtonConst d * (1 + 2 * d) * (vecEuclideanNorm x / 2) ^ (-(d : ℤ)) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (mul_nonneg newtonConst_nonneg (by positivity))
      (zpow_nonneg (by positivity) _)
  -- the formula and the cancellation
  have hform := coordDeriv_newtonPotential hd hF hFc k x
  have hGcont : Continuous G := continuous_pi hGc
  have hGcs : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hR.le) ?_
    intro y hy
    by_contra hne
    have := hGsupp y hne
    apply hy
    have := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le (x₀ := (0 : Vec d)) (x := y)).mpr
      (by simpa only [sub_zero] using this.le)
    exact this
  have hint1 : Integrable (fun y => vecDot (newtonKernel (x - y)) (G y)) volume :=
    integrable_vecDot_newtonKernel_sub hd hGcont hGcs x
  have hint2 : Integrable (fun y => vecDot (newtonKernel x) (G y)) volume := by
    unfold vecDot
    exact integrable_finsetSum _ fun i _ =>
      ((hGc i).integrable_of_hasCompactSupport (hGs i)).const_mul _
  have hzero : ∫ y, vecDot (newtonKernel x) (G y) = 0 := by
    unfold vecDot
    rw [integral_finsetSum _ (fun i _ => ((hGc i).integrable_of_hasCompactSupport (hGs i)).const_mul _)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, hG0 i, mul_zero]
  have hsub : euclideanCoordDeriv k (newtonPotential F) x =
      ∫ y, (vecDot (newtonKernel (x - y)) (G y) - vecDot (newtonKernel x) (G y)) := by
    rw [integral_sub hint1 hint2, hzero, sub_zero, hform]
  have hpt : ∀ y : Vec d, ‖vecDot (newtonKernel (x - y)) (G y) - vecDot (newtonKernel x) (G y)‖ ≤
      K * R * ∑ i : Fin d, |G y i| := by
    intro y
    rw [Real.norm_eq_abs]
    have hnn : 0 ≤ K * R * ∑ i : Fin d, |G y i| :=
      mul_nonneg (mul_nonneg hK0 hR.le) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    by_cases hy : G y = 0
    · have : vecDot (newtonKernel (x - y)) (G y) - vecDot (newtonKernel x) (G y) = 0 := by
        simp [hy, vecDot]
      rw [this, abs_zero]; exact hnn
    · have hyR := hGsupp y hy
      have hv : 2 * vecEuclideanNorm y ≤ vecEuclideanNorm x := by linarith
      have : vecDot (newtonKernel (x - y)) (G y) - vecDot (newtonKernel x) (G y) =
          ∑ i : Fin d, (newtonKernel (x - y) i - newtonKernel x i) * G y i := by
        unfold vecDot
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      have hl := abs_newtonKernel_apply_sub_le i hxpos hv
      have hl' : |newtonKernel (x - y) i - newtonKernel x i| ≤ K * R := by
        refine hl.trans ?_
        have : newtonConst d * (1 + 2 * d) * vecEuclideanNorm y *
            (vecEuclideanNorm x / 2) ^ (-(d : ℤ)) = K * vecEuclideanNorm y := by
          rw [hK]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hyR.le hK0
      calc |newtonKernel (x - y) i - newtonKernel x i| * |G y i|
          ≤ K * R * |G y i| := mul_le_mul_of_nonneg_right hl' (abs_nonneg _)
        _ = _ := by ring
  have hintg : Integrable (fun y => K * R * ∑ i : Fin d, |G y i|) volume :=
    (integrable_finsetSum _ fun i _ => hGint i).const_mul _
  have hb := norm_integral_le_of_norm_le hintg (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hGint i), ← hS] at hb
  rw [hsub]
  refine (Real.norm_eq_abs _ ▸ hb).trans (le_of_eq ?_)
  have hz : (vecEuclideanNorm x / 2) ^ (-(d : ℤ)) = 2 ^ d * vecEuclideanNorm x ^ (-(d : ℝ)) := by
    have : vecEuclideanNorm x ^ (-(d : ℝ)) = vecEuclideanNorm x ^ (-(d : ℤ)) := by
      rw [← Real.rpow_intCast]; push_cast; rfl
    rw [this, div_zpow, zpow_neg, zpow_natCast, zpow_neg (2 : ℝ), zpow_natCast, div_eq_mul_inv,
      inv_inv, mul_comm]
  rw [hK, hz]
  ring

end

end PDE
