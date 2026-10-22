module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Potential.KernelBounds

/-!
# The regularized Newton kernel

`regKernel ε z = z / (d |B₁| (|z|² + ε²)^(d/2))`, a smooth gradient field with
`|regKernel ε z| ≤ |newtonKernel z|` and `regKernel ε → newtonKernel` pointwise as `ε → 0`.
Its divergence is the approximate identity `regDiv ε z = ε² / (|B₁| (|z|² + ε²)^(d/2 + 1))`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE

namespace NewtonRepresentation

noncomputable section

variable {d : ℕ}

/-- The scalar factor of the regularized kernel. -/
def regCoef (d : ℕ) (ε : ℝ) (z : Vec d) : ℝ :=
  newtonConst d * (vecNormSq z + ε ^ 2) ^ (-((d : ℝ) / 2))

/-- The regularized Newton kernel. -/
def regKernel (ε : ℝ) (z : Vec d) : Vec d :=
  regCoef d ε z • z

theorem regCoef_nonneg (ε : ℝ) (z : Vec d) : 0 ≤ regCoef d ε z :=
  mul_nonneg newtonConst_nonneg (Real.rpow_nonneg (by have := vecNormSq_nonneg z; positivity) _)

theorem regCoef_pos (hd : 0 < d) {ε : ℝ} (hε : ε ≠ 0) (z : Vec d) : 0 < regCoef d ε z := by
  have := vecNormSq_nonneg z
  have : 0 < vecNormSq z + ε ^ 2 := by positivity
  exact mul_pos (newtonConst_pos hd) (Real.rpow_pos_of_pos this _)

theorem regKernel_zero_eps (z : Vec d) : regKernel 0 z = newtonKernel z := by
  by_cases hz : z = 0
  · subst hz; simp [regKernel, newtonKernel]
  · rw [regKernel, newtonKernel_eq, regCoef]
    have hn : 0 < vecEuclideanNorm z := vecEuclideanNorm_pos_iff.mpr hz
    have hq : vecNormSq z = vecEuclideanNorm z ^ 2 := (vecEuclideanNorm_sq z).symm
    rw [div_eq_mul_inv]
    congr 2
    rw [← Real.rpow_natCast (vecEuclideanNorm z) d, ← Real.rpow_neg hn.le, hq]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [← Real.rpow_natCast (vecEuclideanNorm z) 2, ← Real.rpow_mul hn.le]
    congr 1
    push_cast
    ring

theorem regCoef_le (hd : 0 < d) (ε : ℝ) {z : Vec d} (hz : z ≠ 0) :
    regCoef d ε z ≤ regCoef d 0 z := by
  have hq : 0 < vecNormSq z := lt_of_le_of_ne (vecNormSq_nonneg z)
    (fun h => hz (vecNormSq_eq_zero h.symm))
  unfold regCoef
  refine mul_le_mul_of_nonneg_left ?_ newtonConst_nonneg
  have hd2 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.rpow_le_rpow_of_nonpos hq (by nlinarith [sq_nonneg ε]) (by linarith)

theorem vecEuclideanNorm_regKernel_le (hd : 0 < d) (ε : ℝ) (z : Vec d) :
    vecEuclideanNorm (regKernel ε z) ≤ vecEuclideanNorm (newtonKernel z) := by
  by_cases hz : z = 0
  · subst hz
    simp [regKernel, newtonKernel, vecEuclideanNorm, vecNormSq, vecDot]
  · rw [← regKernel_zero_eps, regKernel, regKernel, vecEuclideanNorm_smul,
      vecEuclideanNorm_smul, abs_of_nonneg (regCoef_nonneg _ _),
      abs_of_nonneg (regCoef_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regCoef_le hd ε hz) (vecEuclideanNorm_nonneg _)

theorem continuous_regCoef_eps (z : Vec d) (hz : z ≠ 0) :
    Continuous (fun ε : ℝ => regCoef d ε z) := by
  have hq : 0 < vecNormSq z := lt_of_le_of_ne (vecNormSq_nonneg z)
    (fun h => hz (vecNormSq_eq_zero h.symm))
  unfold regCoef
  refine continuous_const.mul ?_
  refine Continuous.rpow_const (by fun_prop) fun ε => Or.inl ?_
  positivity

theorem tendsto_regKernel (z : Vec d) :
    Tendsto (fun ε : ℝ => regKernel ε z) (𝓝 0) (𝓝 (newtonKernel z)) := by
  by_cases hz : z = 0
  · subst hz
    simp only [regKernel, smul_zero, newtonKernel]
    exact tendsto_const_nhds
  · rw [← regKernel_zero_eps]
    have : Continuous (fun ε : ℝ => regKernel ε z) :=
      (continuous_regCoef_eps z hz).smul continuous_const
    exact this.tendsto 0

end

end NewtonRepresentation

end PDE
