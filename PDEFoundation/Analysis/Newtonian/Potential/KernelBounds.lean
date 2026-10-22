module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Kernel.Bridge
public import PDEFoundation.Analysis.RieszWeakType
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.BallVolume

/-!
# Pointwise and integrability bounds for the Newton kernel

`‖E z‖ = c_d |z|^{1-d}` with `c_d = 1 / (d |B₁|)`, hence the kernel components are locally
integrable on `Vec d`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem newtonConst_pos (hd : 0 < d) : 0 < newtonConst d := by
  unfold newtonConst
  have := volume_euclideanBall_toReal_pos (0 : Vec d) (R := 1) one_pos
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem newtonKernel_eq (z : Vec d) :
    newtonKernel z = (newtonConst d / vecEuclideanNorm z ^ d) • z := by
  unfold newtonKernel newtonConst
  congr 1
  rw [one_div, one_div, div_eq_mul_inv, ← mul_inv]

theorem newtonConst_nonneg : 0 ≤ newtonConst d := by
  unfold newtonConst
  positivity

theorem vecEuclideanNorm_newtonKernel_of_ne {z : Vec d} (hz : z ≠ 0) :
    vecEuclideanNorm (newtonKernel z) = newtonConst d * vecEuclideanNorm z ^ ((1 : ℝ) - d) := by
  have hn : 0 < vecEuclideanNorm z := vecEuclideanNorm_pos_iff.mpr hz
  rw [newtonKernel_eq, vecEuclideanNorm_smul, Real.rpow_sub hn, Real.rpow_one,
    Real.rpow_natCast, abs_of_nonneg (div_nonneg newtonConst_nonneg (by positivity))]
  field_simp

theorem vecEuclideanNorm_newtonKernel_le (z : Vec d) :
    vecEuclideanNorm (newtonKernel z) ≤ newtonConst d * vecEuclideanNorm z ^ ((1 : ℝ) - d) := by
  by_cases hz : z = 0
  · subst hz
    have h0 : vecEuclideanNorm (0 : Vec d) = 0 := by simp [vecEuclideanNorm, vecNormSq, vecDot]
    have : vecEuclideanNorm (newtonKernel (0 : Vec d)) = 0 := by
      rw [newtonKernel_eq]; simp [h0]
    rw [this]
    exact mul_nonneg newtonConst_nonneg (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _)
  · exact (vecEuclideanNorm_newtonKernel_of_ne hz).le

theorem measurable_newtonKernel : Measurable (newtonKernel : Vec d → Vec d) := by
  have hn : Measurable (fun z : Vec d => vecEuclideanNorm z) := measurable_vecEuclideanNorm
  have : Measurable (fun z : Vec d => (newtonConst d / vecEuclideanNorm z ^ d)) :=
    measurable_const.div (hn.pow_const d)
  have h2 : Measurable (fun z : Vec d => (newtonConst d / vecEuclideanNorm z ^ d) • z) :=
    this.smul measurable_id
  have h3 : (newtonKernel : Vec d → Vec d) = fun z => (newtonConst d / vecEuclideanNorm z ^ d) • z :=
    funext newtonKernel_eq
  rw [h3]
  exact h2


theorem integrableOn_euclideanBall_rieszKernelOne (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (rieszKernelOne d) (euclideanBall (0 : Vec d) R) := by
  by_cases h1 : d = 1
  · subst h1
    have : rieszKernelOne 1 = fun _ : Vec 1 => (1 : ℝ) := by
      funext z
      simp [rieszKernelOne]
    rw [this]
    exact integrableOn_const (volume_euclideanBall_ne_top _ hR.le).lt_top.ne
  · have hd2 : 2 ≤ d := by omega
    refine (lintegral_ofReal_ne_top_iff_integrable (measurable_rieszKernelOne.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => rieszKernelOne_nonneg z)).mp ?_
    rw [lintegral_euclideanBall_rieszKernelOne hd2 hR]
    exact ENNReal.ofReal_ne_top

theorem integrableOn_euclideanBall_newtonKernel_apply (hd : 0 < d) (i : Fin d) {R : ℝ}
    (hR : 0 < R) :
    IntegrableOn (fun z : Vec d => newtonKernel z i) (euclideanBall (0 : Vec d) R) := by
  refine Integrable.mono' ((integrableOn_euclideanBall_rieszKernelOne hd hR).const_mul
    (newtonConst d)) ?_ ?_
  · exact ((measurable_pi_apply i).comp measurable_newtonKernel).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs]
    exact (abs_apply_le_vecEuclideanNorm _ i).trans (vecEuclideanNorm_newtonKernel_le z)

theorem locallyIntegrable_newtonKernel_apply (hd : 0 < d) (i : Fin d) :
    LocallyIntegrable (fun z : Vec d => newtonKernel z i) volume := by
  intro x
  refine ⟨euclideanBall (0 : Vec d) (vecEuclideanNorm x + 1), ?_,
    integrableOn_euclideanBall_newtonKernel_apply hd i (by have := vecEuclideanNorm_nonneg x; linarith)⟩
  refine (isOpen_euclideanBall _ _).mem_nhds ?_
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by have := vecEuclideanNorm_nonneg x; linarith)]
  simp only [sub_zero]
  linarith

end

end PDE
