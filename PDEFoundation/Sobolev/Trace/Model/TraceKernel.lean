module

public import PDEFoundation.Sobolev.Trace.Model.TraceHorizontal
public import PDEFoundation.Sobolev.Trace.Model.TraceAlgebra

/-!
# Step 3, the kernel bound

Pointwise in `(x', y')`, the Gagliardo integrand is bounded by `2^{2(p-1)}` times the sum of the
two vertical terms `traceVert` and the horizontal term `traceHoriz`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- The vertical term `(∫_0^h |∂ₜ v(b, ·)|)^p h^{-(n+p-1)}` with `h = |y' - x'|`, based at `b`. -/
noncomputable def traceVert (v : Vec n × ℝ → ℝ) (p : ℝ) (b : Vec n) (h : ℝ) : ℝ≥0∞ :=
  vertInt v b h ^ p * ENNReal.ofReal (h ^ (-((n : ℝ) + p - 1)))

/-- The horizontal term `h^{1-n} ∫_0^1 |∇'v(x' + θ(y'-x'), h)|^p dθ`. -/
noncomputable def traceHoriz (v : Vec n × ℝ → ℝ) (p : ℝ) (x' y' : Vec n) : ℝ≥0∞ :=
  ENNReal.ofReal (vecEuclideanNorm (y' - x') ^ (1 - (n : ℝ))) *
    ∫⁻ θ in Ioc (0 : ℝ) 1, tanGradPow v p (x' + θ • (y' - x'), vecEuclideanNorm (y' - x'))

/-- Pointwise kernel bound. -/
theorem integrand_le {p : ℝ} (hp : 1 < p) {v : Vec n × ℝ → ℝ}
    (hv : ContDiffOn ℝ 1 v (closedUpperHalf n)) (x' y' : Vec n) :
    ENNReal.ofReal (|v (x', 0) - v (y', 0)| ^ p / vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1)) ≤
      (2 ^ (p - 1) * 2 ^ (p - 1)) *
        (traceVert v p x' (vecEuclideanNorm (y' - x')) + traceHoriz v p x' y' +
          traceVert v p y' (vecEuclideanNorm (y' - x'))) := by
  have hp0 : 0 < p := by linarith
  by_cases hxy : x' = y'
  · subst hxy
    simp [Real.zero_rpow hp0.ne']
  set h := vecEuclideanNorm (y' - x') with hh
  have hpos : 0 < h := vecEuclideanNorm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hsymm : vecEuclideanNorm (x' - y') = h := vecEuclideanNorm_sub_comm x' y'
  set J := ∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (tanGradNorm v (x' + θ • (y' - x'), h)) with hJ
  have hpt := ofReal_abs_boundary_sub_le hv x' y' hxy
  rw [← hh] at hpt
  -- split the integrand
  have hrewrite : ENNReal.ofReal (|v (x', 0) - v (y', 0)| ^ p /
        vecEuclideanNorm (x' - y') ^ ((n : ℝ) + p - 1)) =
      ENNReal.ofReal |v (x', 0) - v (y', 0)| ^ p * ENNReal.ofReal (h ^ (-((n : ℝ) + p - 1))) := by
    rw [hsymm, div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le, Real.rpow_neg hpos.le]
  rw [hrewrite]
  have h1 : ENNReal.ofReal |v (x', 0) - v (y', 0)| ^ p ≤
      (vertInt v x' h + ENNReal.ofReal h * J + vertInt v y' h) ^ p :=
    ENNReal.rpow_le_rpow hpt hp0.le
  have h2 := three_rpow_le hp.le (vertInt v x' h) (ENNReal.ofReal h * J) (vertInt v y' h)
  have hJae : AEMeasurable (fun θ : ℝ => ENNReal.ofReal (tanGradNorm v (x' + θ • (y' - x'), h)))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine Measurable.aemeasurable (ENNReal.measurable_ofReal.comp
      ((measurable_tanGradNorm v).comp (Measurable.prodMk ?_ measurable_const)))
    exact measurable_const.add (measurable_id.smul measurable_const)
  have hJensen := lintegral_Ioc_unit_rpow_le hp.le hJae
  have hmid : (ENNReal.ofReal h * J) ^ p ≤
      ENNReal.ofReal (h ^ p) * ∫⁻ θ in Ioc (0 : ℝ) 1,
        tanGradPow v p (x' + θ • (y' - x'), h) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg hpos.le hp0.le]
    refine mul_le_mul_right ?_ _
    refine hJensen.trans (le_of_eq (lintegral_congr (fun θ => ?_)))
    simp only [tanGradPow]
    rw [ENNReal.ofReal_rpow_of_nonneg (by simp [tanGradNorm, vecEuclideanNorm_nonneg]) hp0.le]
  have hexp : h ^ p * h ^ (-((n : ℝ) + p - 1)) = h ^ (1 - (n : ℝ)) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  calc ENNReal.ofReal |v (x', 0) - v (y', 0)| ^ p * ENNReal.ofReal (h ^ (-((n : ℝ) + p - 1)))
      ≤ ((2 ^ (p - 1) * 2 ^ (p - 1)) * (vertInt v x' h ^ p + (ENNReal.ofReal h * J) ^ p +
          vertInt v y' h ^ p)) * ENNReal.ofReal (h ^ (-((n : ℝ) + p - 1))) :=
        mul_le_mul_left (h1.trans h2) _
    _ ≤ ((2 ^ (p - 1) * 2 ^ (p - 1)) * (vertInt v x' h ^ p +
          ENNReal.ofReal (h ^ p) * (∫⁻ θ in Ioc (0 : ℝ) 1,
            tanGradPow v p (x' + θ • (y' - x'), h)) + vertInt v y' h ^ p)) *
          ENNReal.ofReal (h ^ (-((n : ℝ) + p - 1))) := by
        gcongr
    _ = (2 ^ (p - 1) * 2 ^ (p - 1)) * (traceVert v p x' h + traceHoriz v p x' y' +
          traceVert v p y' h) := by
        have hmulh : ENNReal.ofReal (h ^ p) * ENNReal.ofReal (h ^ (-((n : ℝ) + p - 1))) =
            ENNReal.ofReal (h ^ (1 - (n : ℝ))) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), hexp]
        simp only [traceVert, traceHoriz, ← hh]
        rw [← hmulh]
        ring

end PDE.TraceLane
