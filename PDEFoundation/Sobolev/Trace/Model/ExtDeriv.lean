module

public import PDEFoundation.Sobolev.Trace.Model.ExtSmooth
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiation of the extension under the integral sign

`dilConv n ρ g` is `C¹` on the open upper half-space, with derivative the integral of the
derivative of the kernel against `g`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ}

theorem norm_dilFDeriv_le {M : ℝ}
    (hM : ∀ w : Vec n, ‖fderiv ℝ (extKernel n) w‖ ≤ M ∧ |extRad n w| ≤ M) {z : Vec n} {t : ℝ}
    (ht : 0 < t) : ‖dilFDeriv n (z, t)‖ ≤ (t⁻¹) ^ (n + 1) * (M + M) := by
  unfold dilFDeriv
  rw [norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg ht.le]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := Vec n) (F := ℝ))
        (norm_nonneg _)).trans (by simpa only [mul_one] using (hM (t⁻¹ • z)).1))
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := Vec n) (F := ℝ))
      (abs_nonneg _)).trans (by simpa only [mul_one] using (hM (t⁻¹ • z)).2)

theorem dilFDeriv_eq_zero {z : Vec n} {t : ℝ} (ht : 0 < t) (hz : t < vecEuclideanNorm z) :
    dilFDeriv n (z, t) = 0 := by
  have hw : 1 < vecEuclideanNorm (t⁻¹ • z) := by
    rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 ht), ← div_eq_inv_mul, one_lt_div ht]
    exact hz
  simp [dilFDeriv, fderiv_extKernel_eq_zero_of_one_lt n hw, extRad_eq_zero_of_one_lt n hw]

theorem exists_dilFDeriv_bound {g : Vec n → ℝ} (hg : LocallyIntegrable g volume)
    {p₀ : Vec n × ℝ} (h0 : 0 < p₀.2) :
    ∃ bnd : Vec n → ℝ, Integrable bnd volume ∧
      ∀ q ∈ Metric.ball p₀ (p₀.2 / 2), ∀ y, ‖g y • dilFDeriv n (q.1 - y, q.2)‖ ≤ bnd y := by
  obtain ⟨M, -, hM⟩ := exists_extKernel_bound n
  have hM' : ∀ w : Vec n, ‖fderiv ℝ (extKernel n) w‖ ≤ M ∧ |extRad n w| ≤ M :=
    fun w => ⟨(hM w).1, (hM w).2.2⟩
  set B : ℝ := (2 / p₀.2) ^ (n + 1) * (M + M) with hB
  refine ⟨(Metric.closedBall p₀.1 (2 * p₀.2)).indicator (fun y => B * ‖g y‖), ?_, ?_⟩
  · have hI : IntegrableOn (fun y => ‖g y‖) (Metric.closedBall p₀.1 (2 * p₀.2)) volume :=
      (hg.integrableOn_isCompact (isCompact_closedBall _ _)).norm
    exact IntegrableOn.integrable_indicator (hI.const_mul B) measurableSet_closedBall
  · intro q hq y
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Real.dist_eq, abs_lt] at hq2
    have hqpos : 0 < q.2 := by linarith [hq2.1]
    by_cases hy : y ∈ Metric.closedBall p₀.1 (2 * p₀.2)
    · rw [Set.indicator_of_mem hy, norm_smul]
      have h1 := norm_dilFDeriv_le hM' (z := q.1 - y) hqpos
      have h2 : (q.2⁻¹) ^ (n + 1) ≤ (2 / p₀.2) ^ (n + 1) := by
        refine pow_le_pow_left₀ (inv_nonneg.2 hqpos.le) ?_ _
        rw [inv_eq_one_div, div_le_div_iff₀ hqpos h0]
        linarith [hq2.1]
      have h3 : ‖dilFDeriv n (q.1 - y, q.2)‖ ≤ B := by
        refine h1.trans ?_
        exact mul_le_mul_of_nonneg_right h2 (by
          have := (hM 0).1
          have h4 := norm_nonneg (fderiv ℝ (extKernel n) 0)
          linarith)
      calc ‖g y‖ * ‖dilFDeriv n (q.1 - y, q.2)‖ ≤ ‖g y‖ * B :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = B * ‖g y‖ := mul_comm _ _
    · rw [Set.indicator_of_notMem hy]
      have hy' : 2 * p₀.2 < ‖y - p₀.1‖ := by simpa [dist_eq_norm] using hy
      have hq1' : ‖q.1 - p₀.1‖ < p₀.2 / 2 := by simpa [dist_eq_norm] using hq1
      have h5 : q.2 < vecEuclideanNorm (q.1 - y) := by
        refine lt_of_lt_of_le ?_ (norm_le_vecEuclideanNorm _)
        have : ‖y - p₀.1‖ ≤ ‖q.1 - y‖ + ‖q.1 - p₀.1‖ := by
          calc ‖y - p₀.1‖ = ‖(q.1 - p₀.1) - (q.1 - y)‖ := by congr 1; abel
            _ ≤ ‖q.1 - p₀.1‖ + ‖q.1 - y‖ := norm_sub_le _ _
            _ = _ := add_comm _ _
        linarith [hq2.2]
      rw [dilFDeriv_eq_zero hqpos h5]
      simp

theorem continuousAt_dilFDeriv {p : Vec n × ℝ} (hp : p.2 ≠ 0) :
    ContinuousAt (dilFDeriv n) p := by
  have hw : ContinuousAt (fun q : Vec n × ℝ => q.2⁻¹ • q.1) p :=
    ((continuous_snd.continuousAt).inv₀ hp).smul continuous_fst.continuousAt
  have h1 : ContinuousAt (fun q : Vec n × ℝ => fderiv ℝ (extKernel n) (q.2⁻¹ • q.1)) p :=
    (continuous_fderiv_extKernel n).continuousAt.comp hw
  have h2 : ContinuousAt (fun q : Vec n × ℝ => extRad n (q.2⁻¹ • q.1)) p :=
    (continuous_extRad n).continuousAt.comp hw
  have h3 : ContinuousAt (fun q : Vec n × ℝ => (q.2⁻¹) ^ (n + 1)) p :=
    ((continuous_snd.continuousAt).inv₀ hp).pow _
  unfold dilFDeriv
  exact h3.smul ((h1.clm_comp continuousAt_const).add (h2.smul continuousAt_const))

theorem hasFDerivAt_extConv {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) {p : Vec n × ℝ}
    (hp : 0 < p.2) :
    HasFDerivAt (dilConv n (extKernel n) g) (∫ y, g y • dilFDeriv n (p.1 - y, p.2)) p := by
  obtain ⟨bnd, hbi, hb⟩ := exists_dilFDeriv_bound hg hp
  have hs : Metric.ball p (p.2 / 2) ∈ 𝓝 p := Metric.ball_mem_nhds _ (by positivity)
  have hcont : Continuous fun y : Vec n => dilFDeriv n (p.1 - y, p.2) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have h1 : ContinuousAt (fun y : Vec n => (p.1 - y, p.2)) y :=
      (continuous_const.sub continuous_id).continuousAt.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun y : Vec n => (p.1 - y, p.2)) (x := y)
      (continuousAt_dilFDeriv (n := n) (p := (p.1 - y, p.2)) hp.ne') h1
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q y => dil n (extKernel n) (q.1 - y) q.2 * g y)
    (F' := fun q y => g y • dilFDeriv n (q.1 - y, q.2)) hs ?_ ?_ ?_ ?_ hbi ?_
  · exact Filter.Eventually.of_forall fun q =>
      (continuous_dil_sub n (isProfile_extKernel n) q.2 q.1).aestronglyMeasurable.mul
        hg.aestronglyMeasurable
  · exact integrable_dil_mul n (isProfile_extKernel n) hp hg p.1
  · exact hg.aestronglyMeasurable.smul hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y q hq => hb q hq y
  · refine Filter.Eventually.of_forall fun y q hq => ?_
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hq
    have hqpos : q.2 ≠ 0 := by linarith [hq.2.1]
    have hlin : HasFDerivAt (fun x : Vec n × ℝ => (x.1 - y, x.2))
        ((ContinuousLinearMap.fst ℝ (Vec n) ℝ).prod (ContinuousLinearMap.snd ℝ (Vec n) ℝ)) q :=
      (hasFDerivAt_fst.sub_const y).prodMk hasFDerivAt_snd
    have := ((hasFDerivAt_dil_kernel n (p := (q.1 - y, q.2)) hqpos).comp q hlin).mul_const (g y)
    refine this.congr_fderiv ?_
    simp

end PDE.TraceLane
