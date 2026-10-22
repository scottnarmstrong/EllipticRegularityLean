module

public import PDEFoundation.Sobolev.Trace.Model.TraceMeasurable
public import PDEFoundation.Sobolev.Trace.Model.Hardy

/-!
# Step 3, vertical terms

For fixed `b : Vec n`, polar coordinates in `k` followed by Hardy's inequality give
`∫ (∫_0^{|k|} |∂ₜ v(b, ·)|)^p |k|^{-(n+p-1)} dk ≤ c (p/(p-1))^p ∫_0^∞ |∂ₜ v(b, t)|^p dt`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- For `r > 0`, `r^{n-1} (V^p r^{-(n+p-1)}) = (V / r)^p`. -/
theorem vertical_weight_eq [NeZero n] {p : ℝ} (hp : 1 < p) (V : ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ (n - 1)) * (V ^ p * ENNReal.ofReal (r ^ (-((n : ℝ) + p - 1)))) =
      (V / ENNReal.ofReal r) ^ p := by
  have hp0 : 0 < p := by linarith
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hrp : ((ENNReal.ofReal r)⁻¹) ^ p = ENNReal.ofReal (r ^ (-p)) := by
    rw [ENNReal.inv_rpow, ENNReal.ofReal_rpow_of_nonneg hr.le hp0.le, Real.rpow_neg hr.le,
      ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr _)]
  have hexp : r ^ (n - 1) * r ^ (-((n : ℝ) + p - 1)) = r ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, Nat.cast_sub hn]
    congr 1
    push_cast
    ring
  rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hrp, mul_left_comm,
    ← ENNReal.ofReal_mul (by positivity), hexp]

/-- Vertical bound. -/
theorem vertical_bound [NeZero n] {p : ℝ} (hp : 1 < p) (c : ℝ≥0∞)
    (hc : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∫⁻ k : Vec n, f (vecEuclideanNorm k) =
      c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r)
    (v : Vec n × ℝ → ℝ) (b : Vec n) :
    ∫⁻ k : Vec n, vertInt v b (vecEuclideanNorm k) ^ p *
        ENNReal.ofReal (vecEuclideanNorm k ^ (-((n : ℝ) + p - 1))) ≤
      c * ENNReal.ofReal ((p / (p - 1)) ^ p) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (|normDeriv v (b, t)| ^ p) := by
  have hp0 : 0 < p := by linarith
  set f : ℝ → ℝ≥0∞ := fun r => vertInt v b r ^ p * ENNReal.ofReal (r ^ (-((n : ℝ) + p - 1)))
    with hf
  have hfm : Measurable f :=
    (((measurable_vertInt v).comp (measurable_const.prodMk measurable_id)).pow_const p).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  have h1 := hc f hfm
  simp only [hf] at h1
  rw [h1, mul_assoc]
  refine mul_le_mul_right ?_ c
  have h2 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r =
      ∫⁻ r in Ioi (0 : ℝ), (vertInt v b r / ENNReal.ofReal r) ^ p := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    exact vertical_weight_eq hp _ hr
  rw [h2]
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal |normDeriv v (b, t)| with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((measurable_normDeriv v).comp (measurable_const.prodMk measurable_id)))
  have h3 := hardy_lintegral hp g hgm
  have h4 : ∫⁻ t in Ioi (0 : ℝ), g t ^ p = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (|normDeriv v (b, t)| ^ p) := by
    refine lintegral_congr (fun t => ?_)
    simp only [hg]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
  rw [h4] at h3
  exact h3

end PDE.TraceLane
