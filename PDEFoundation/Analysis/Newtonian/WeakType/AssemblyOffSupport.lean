module

public import PDEFoundation.Analysis.Newtonian.WeakType.HormanderKernel
public import PDEFoundation.Analysis.Newtonian.NewtonKernelDerivProof
public import PDEFoundation.Analysis.Newtonian.NewtonKernelHolderProof
public import PDEFoundation.Analysis.Newtonian.Potential.Smooth
public import PDEFoundation.Analysis.Newtonian.Potential.Decay
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The gradient of the Newtonian potential away from the support

If `h` is smooth with compact support and `x` has Euclidean distance at least `δ > 0` from the
support of `h`, then `∂_k u_h (x) = ∫ (∇E)(x - y) h(y) dy` (row `k`).  This is differentiation under
the integral sign, using the derivative formula `D1a` of the kernel.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem newtonKernelJacobian_symm (z : Vec d) (i j : Fin d) :
    newtonKernelJacobian z i j = newtonKernelJacobian z j i := by
  unfold newtonKernelJacobian
  have : (if i = j then (1 : ℝ) else 0) = if j = i then 1 else 0 := by
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, mul_comm (z i) (z j)]

theorem abs_newtonKernelJacobian_le (z : Vec d) (i j : Fin d) :
    |newtonKernelJacobian z i j| ≤
      (1 + d) * (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal *
        vecEuclideanNorm z ^ d))⁻¹ := by
  unfold newtonKernelJacobian
  set D : ℝ := (d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal * vecEuclideanNorm z ^ d
    with hD
  have hD0 : 0 ≤ D := by
    have := (ENNReal.toReal_nonneg : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal)
    have := vecEuclideanNorm_nonneg z
    positivity
  rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (inv_nonneg.mpr hD0)]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hD0)
  have h1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have h2 : |(d : ℝ) * (z i * z j) / vecNormSq z| ≤ d := by
    by_cases hz : vecNormSq z = 0
    · simp [hz]
    · have hpos : 0 < vecNormSq z := lt_of_le_of_ne (vecNormSq_nonneg z) (Ne.symm hz)
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
      have hzi := abs_apply_le_vecEuclideanNorm z i
      have hzj := abs_apply_le_vecEuclideanNorm z j
      have : |z i * z j| ≤ vecNormSq z := by
        rw [abs_mul, ← vecEuclideanNorm_sq]
        calc |z i| * |z j| ≤ vecEuclideanNorm z * vecEuclideanNorm z :=
              mul_le_mul hzi hzj (abs_nonneg _) (vecEuclideanNorm_nonneg _)
          _ = vecEuclideanNorm z ^ 2 := by ring
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)
  calc |(if i = j then (1 : ℝ) else 0) - (d : ℝ) * (z i * z j) / vecNormSq z|
      ≤ |(if i = j then (1 : ℝ) else 0)| + |(d : ℝ) * (z i * z j) / vecNormSq z| := abs_sub _ _
    _ ≤ 1 + d := add_le_add h1 h2

theorem hasDerivAt_vecDot_newtonKernel_line (hd : 0 < d) {w : Vec d} (k : Fin d) (s₀ : ℝ)
    (hne : w + s₀ • basisVec k ≠ 0) (c : Vec d) :
    HasDerivAt (fun s : ℝ => vecDot (newtonKernel (w + s • basisVec k)) c)
      (vecDot (fun i => newtonKernelJacobian (w + s₀ • basisVec k) i k) c) s₀ := by
  have hE := (NewtonKernelDerivProof.result d hd).2 _ hne
  have hl : HasDerivAt (fun s : ℝ => w + s • basisVec k) (basisVec k) s₀ := by
    have := ((hasDerivAt_id s₀).smul_const (basisVec k)).const_add w
    simpa using this
  have hc := hE.comp_hasDerivAt s₀ hl
  have hcomp : HasDerivAt (fun s : ℝ => newtonKernel (w + s • basisVec k))
      (fun i => newtonKernelJacobian (w + s₀ • basisVec k) i k) s₀ := by
    refine HasDerivAt.congr_deriv hc ?_
    funext i
    simp [basisVec]
  unfold vecDot
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasDerivAt_pi.mp hcomp i).mul_const (c i)))
  simpa using this

theorem classicalGradient_newtonPotential_eq_of_far (hd : 0 < d) {h : Vec d → Vec d}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) {x : Vec d} {δ : ℝ} (hδ : 0 < δ)
    (hfar : ∀ y, h y ≠ 0 → δ ≤ vecEuclideanNorm (x - y)) (k : Fin d) :
    Integrable (fun y => matVecMul (newtonKernelJacobian (x - y)) (h y) k) volume ∧
    classicalGradient (newtonPotential h) x k =
      ∫ y, matVecMul (newtonKernelJacobian (x - y)) (h y) k := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨A, hA0, hA⟩ := NewtonKernelHolderProof.result d hd
  have hK : KernelHolder d newtonKernelJacobian A := fun z z' hz hzz v => hA z z' hz hzz v
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hV0 : 0 < V := volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hcont : Continuous h := hh.continuous
  have hhi : ∀ i, Continuous fun y => h y i := fun i => (contDiff_pi.mp hh i).continuous
  set F : ℝ → Vec d → ℝ := fun s y =>
    vecDot (newtonKernel ((x - y) + s • basisVec k)) (h y) with hF
  set F' : ℝ → Vec d → ℝ := fun s y =>
    vecDot (fun i => newtonKernelJacobian ((x - y) + s • basisVec k) i k) (h y) with hF'
  set Cδ : ℝ := (1 + d) * ((d : ℝ) * V * (δ / 2) ^ d)⁻¹ with hCδ
  set bound : Vec d → ℝ := fun y => Cδ * ∑ i : Fin d, |h y i| with hbound
  have hFeq : ∀ s, (∫ y, F s y) = newtonPotential h (x + s • basisVec k) := by
    intro s
    unfold newtonPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, add_sub_right_comm]
  have hFint : ∀ s, Integrable (F s) volume := by
    intro s
    have := integrable_vecDot_newtonKernel_sub hd hcont hhc (x + s • basisVec k)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, add_sub_right_comm]
  have hnorm : ∀ y, h y ≠ 0 → ∀ s : ℝ, |s| < δ / 2 →
      δ / 2 ≤ vecEuclideanNorm ((x - y) + s • basisVec k) := by
    intro y hy s hs
    have h1 := hfar y hy
    have h2 : vecEuclideanNorm (x - y) ≤ vecEuclideanNorm ((x - y) + s • basisVec k) + |s| := by
      have := vecEuclideanNorm_add_le ((x - y) + s • basisVec k) (-(s • basisVec k))
      rw [vecEuclideanNorm_neg, vecEuclideanNorm_smul, vecEuclideanNorm_basisVec, mul_one] at this
      simpa using this
    linarith
  have hbd : ∀ y, ∀ s : ℝ, |s| < δ / 2 → ‖F' s y‖ ≤ bound y := by
    intro y s hs
    by_cases hy : h y = 0
    · have : F' s y = 0 := by simp [hF', vecDot, hy]
      rw [this, norm_zero]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    · have hz := hnorm y hy s hs
      have hzpos : 0 < vecEuclideanNorm ((x - y) + s • basisVec k) := by linarith
      rw [Real.norm_eq_abs]
      calc |F' s y| = |∑ i : Fin d, newtonKernelJacobian ((x - y) + s • basisVec k) i k * h y i| := rfl
        _ ≤ ∑ i : Fin d, |newtonKernelJacobian ((x - y) + s • basisVec k) i k * h y i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin d, Cδ * |h y i| := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            refine (abs_newtonKernelJacobian_le _ i k).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine inv_anti₀ (by positivity) ?_
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz d) (by positivity)
        _ = bound y := by show _ = Cδ * _; rw [Finset.mul_sum]
  have hbint : Integrable bound volume := by
    refine Integrable.const_mul (integrable_finsetSum _ fun i _ => ?_) _
    exact ((hhi i).integrable_of_hasCompactSupport
      (hasCompactSupport_apply hhc i)).abs
  have hdiff : ∀ y, ∀ s ∈ ball (0 : ℝ) (δ / 2), HasDerivAt (fun s => F s y) (F' s y) s := by
    intro y s hs
    have hs' : |s| < δ / 2 := by simpa [Real.dist_eq] using hs
    by_cases hy : h y = 0
    · have h0 : (fun s => F s y) = fun _ => 0 := by funext t; simp [hF, vecDot, hy]
      have h1 : F' s y = 0 := by simp [hF', vecDot, hy]
      rw [h0, h1]
      exact hasDerivAt_const _ _
    · have hz := hnorm y hy s hs'
      exact hasDerivAt_vecDot_newtonKernel_line hd (w := x - y) k s (by
        intro h0
        rw [h0] at hz
        have : vecEuclideanNorm (0 : Vec d) = 0 := by simp [vecEuclideanNorm, vecNormSq, vecDot]
        linarith) (h y)
  have hF'meas : AEStronglyMeasurable (F' 0) volume := by
    have : F' 0 = fun y => ∑ i : Fin d, newtonKernelJacobian (x - y) i k * h y i := by
      funext y; simp [hF', vecDot]
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (hK.aestronglyMeasurable_entry x i k).mul (hhi i).aestronglyMeasurable
  have hFp : ∀ y, F' 0 y = matVecMul (newtonKernelJacobian (x - y)) (h y) k := by
    intro y
    simp only [hF', zero_smul, add_zero, vecDot, matVecMul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [newtonKernelJacobian_symm]
  have hmain0 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := 0) (ball_mem_nhds (0 : ℝ) (half_pos hδ)) (Filter.Eventually.of_forall fun s => (hFint s).aestronglyMeasurable)
    (hFint 0) hF'meas
    (Filter.Eventually.of_forall fun y s hs => hbd y s (by simpa [Real.dist_eq] using hs))
    hbint (Filter.Eventually.of_forall hdiff))
  have hmain := hmain0.2
  have hu := contDiff_newtonPotential hd hh hhc
  have hline : HasDerivAt (fun s : ℝ => newtonPotential h (x + s • basisVec k))
      (fderiv ℝ (newtonPotential h) x (basisVec k)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => x + s • basisVec k) (basisVec k) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec k)).const_add x
      simpa using this
    have hf := ((hu.differentiable (by simp)) x).hasFDerivAt
    have hf' : HasFDerivAt (newtonPotential h) (fderiv ℝ (newtonPotential h) x)
        (x + (0 : ℝ) • basisVec k) := by simpa using hf
    exact hf'.comp_hasDerivAt (0 : ℝ) hl
  have hmain' : HasDerivAt (fun s : ℝ => newtonPotential h (x + s • basisVec k))
      (∫ y, F' 0 y) 0 := by
    have : (fun s : ℝ => ∫ y, F s y) = fun s => newtonPotential h (x + s • basisVec k) :=
      funext hFeq
    rwa [this] at hmain
  have := hline.unique hmain'
  refine ⟨hmain0.1.congr (Filter.Eventually.of_forall hFp), ?_⟩
  show fderiv ℝ (newtonPotential h) x (basisVec k) = _
  rw [this]
  exact integral_congr_ae (Filter.Eventually.of_forall hFp)

end

end PDE.NewtonWeakType
