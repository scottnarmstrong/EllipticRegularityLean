module

public import PDEFoundation.Sobolev.Trace.Model.TraceMeasurable

/-!
# Step 3, the horizontal term

Exchange of integrals, translation invariance in `x'` and polar coordinates in `k` give
`∫∫ |k|^{1-n} ∫_0^1 |∇'v(x' + θk, |k|)|^p dθ dk dx' = c ∫_{ℝ^n × (0,∞)} |∇'v|^p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- `|∇'v|^p` as an extended nonnegative function. -/
noncomputable def tanGradPow (v : Vec n × ℝ → ℝ) (p : ℝ) (z : Vec n × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (tanGradNorm v z ^ p)

theorem measurable_tanGradPow (v : Vec n × ℝ → ℝ) (p : ℝ) : Measurable (tanGradPow v p) :=
  ENNReal.measurable_ofReal.comp ((measurable_tanGradNorm v).pow_const p)

/-- The horizontal term. -/
theorem horizontal_eq [NeZero n] (p : ℝ) (c : ℝ≥0∞)
    (hc : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∫⁻ k : Vec n, f (vecEuclideanNorm k) =
      c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r)
    (v : Vec n × ℝ → ℝ) :
    ∫⁻ x' : Vec n, ∫⁻ k : Vec n, ENNReal.ofReal (vecEuclideanNorm k ^ (1 - (n : ℝ))) *
        ∫⁻ θ in Ioc (0 : ℝ) 1, tanGradPow v p (x' + θ • k, vecEuclideanNorm k) =
      c * ∫⁻ z in upperHalf n, tanGradPow v p z := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  set Gp := tanGradPow v p with hGp
  have hGm : Measurable Gp := measurable_tanGradPow v p
  -- joint measurability of the inner `θ`-integral
  have hJ : Measurable (fun q : Vec n × Vec n =>
      ∫⁻ θ in Ioc (0 : ℝ) 1, Gp (q.1 + θ • q.2, vecEuclideanNorm q.2)) := by
    have hf : Measurable (fun r : (Vec n × Vec n) × ℝ =>
        Gp (r.1.1 + r.2 • r.1.2, vecEuclideanNorm r.1.2)) := by
      refine hGm.comp (Measurable.prodMk ?_ ?_)
      · exact (measurable_fst.comp measurable_fst).add
          (measurable_snd.smul (measurable_snd.comp measurable_fst))
      · exact measurable_vecEuclideanNorm.comp (measurable_snd.comp measurable_fst)
    exact hf.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  have hFm : Measurable (fun q : Vec n × Vec n =>
      ENNReal.ofReal (vecEuclideanNorm q.2 ^ (1 - (n : ℝ))) *
        ∫⁻ θ in Ioc (0 : ℝ) 1, Gp (q.1 + θ • q.2, vecEuclideanNorm q.2)) :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_vecEuclideanNorm.comp measurable_snd).pow_const _)).mul hJ
  -- exchange `x'` and `k`
  rw [lintegral_lintegral_swap (f := fun x' k => ENNReal.ofReal (vecEuclideanNorm k ^ (1 - (n : ℝ))) *
      ∫⁻ θ in Ioc (0 : ℝ) 1, Gp (x' + θ • k, vecEuclideanNorm k)) hFm.aemeasurable]
  -- the inner `x'`-integral, for fixed `k`
  set Φ : ℝ → ℝ≥0∞ := fun r => ∫⁻ z' : Vec n, Gp (z', r) with hΦ
  have hinner : ∀ k : Vec n, ∫⁻ x' : Vec n, ENNReal.ofReal (vecEuclideanNorm k ^ (1 - (n : ℝ))) *
      ∫⁻ θ in Ioc (0 : ℝ) 1, Gp (x' + θ • k, vecEuclideanNorm k) =
      ENNReal.ofReal (vecEuclideanNorm k ^ (1 - (n : ℝ))) * Φ (vecEuclideanNorm k) := by
    intro k
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hm : Measurable (fun r : Vec n × ℝ => Gp (r.1 + r.2 • k, vecEuclideanNorm k)) :=
      hGm.comp (((measurable_fst.add (measurable_snd.smul measurable_const))).prodMk
        measurable_const)
    rw [lintegral_lintegral_swap (f := fun x' θ => Gp (x' + θ • k, vecEuclideanNorm k))
      hm.aemeasurable]
    have htrans : ∀ θ : ℝ, ∫⁻ x' : Vec n, Gp (x' + θ • k, vecEuclideanNorm k) = Φ (vecEuclideanNorm k) :=
      fun θ => lintegral_add_right_eq_self (fun z' => Gp (z', vecEuclideanNorm k)) (θ • k)
    simp only [htrans, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.ofReal_one, mul_one]
  simp only [hinner]
  have hΦm : Measurable Φ := Measurable.lintegral_prod_left' (f := fun q : Vec n × ℝ => Gp q) hGm
  have hfm : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ (1 - (n : ℝ))) * Φ r) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul hΦm
  rw [hc (fun r => ENNReal.ofReal (r ^ (1 - (n : ℝ))) * Φ r) hfm]
  congr 1
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) *
      (ENNReal.ofReal (r ^ (1 - (n : ℝ))) * Φ r) = Φ r := by
    intro r hr
    have hr0 : 0 < r := hr
    have hexp : r ^ (n - 1) * r ^ (1 - (n : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0, Nat.cast_sub hn]
      simp
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hexp, ENNReal.ofReal_one, one_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  -- `∫_0^∞ ∫ Gp = ∫_{upper half} Gp`
  rw [lintegral_upperHalf Gp hGm.aemeasurable]
  simp only [hΦ]
  exact lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure (Vec n)))
    (f := fun r z' => Gp (z', r)) (by
      exact (hGm.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)

end PDE.TraceLane
