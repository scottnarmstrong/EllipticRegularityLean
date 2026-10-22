module

public import PDEFoundation.PDE.HarmonicGradientOscillationSmooth
public import PDEFoundation.PDE.HarmonicEnergy
public import PDEFoundation.Sobolev.H1.OscillationComparison

/-! # Exact centered gradient decay for weak harmonic functions -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- Smooth convex approximants converge to the weak gradient in normalized
Euclidean root-mean-square energy on every measurable subdomain. -/
theorem tendsto_convexApproxSmoothW1p_sqrt_integralAverage_grad_sub
    {U V : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (hVU : V ⊆ U)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Tendsto (fun n => Real.sqrt (integralAverage V (fun x => vecNormSq
      ((W1pFunction.convexApproxSmoothW1p hU (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        u.toW1pFunction x0 hr n).grad x - u.grad x)))) atTop (𝓝 0) := by
  let v := W1pFunction.convexApproxSmoothW1p hU
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) u.toW1pFunction x0 hr
  let E : ℕ → Vec d → Vec d := fun n x => (v n).grad x - u.grad x
  have hconv (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => E n x i) 2 (volumeOn V)) atTop (𝓝 0) := by
    have hwhole := W1pFunction.tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
      hU (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      u.toW1pFunction hball hr i
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwhole
      (fun _ => bot_le)
    intro n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
  have hE (n : ℕ) : MemVectorL2On V (E n) := fun i => by
    dsimp only [E]
    exact (memLpOn_mono hVU ((v n).grad_memLp i)).sub
      (memLpOn_mono hVU (u.gradMemL2 i))
  have hzero : MemVectorL2On V (fun _ : Vec d => (0 : Vec d)) := fun _ =>
    MeasureTheory.MemLp.zero
  have hraw := tendsto_setIntegral_vecNormSq_of_tendsto_eLpNorm
    hE hzero (fun i => by simpa only [Pi.zero_apply, sub_zero] using hconv i)
  have havg : Tendsto (fun n => integralAverage V (fun x => vecNormSq (E n x)))
      atTop (𝓝 0) := by
    simpa only [integralAverage, vecNormSq, vecDot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, integral_zero, mul_zero] using hraw.const_mul (volume V).toReal⁻¹
  simpa only [E, Real.sqrt_zero] using havg.sqrt

private theorem centeredVectorMeanL2_weakHarmonic_grad_decay_of_lt [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    centeredVectorMeanL2 (euclideanBall z a) u.grad ≤
      (a / b) * centeredVectorMeanL2 (euclideanBall z b) u.grad := by
  let hU := isOpenBoundedConvexDomain_euclideanBall z hR
  obtain ⟨x0, r, hr, hball⟩ :=
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain hU
      (euclideanBall_nonempty z hR)
  let v := W1pFunction.convexApproxSmoothW1p hU
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) u.toW1pFunction x0 hr
  let err : ℕ → Vec d → Vec d := fun n x => u.grad x - (v n).grad x
  have hba : euclideanBall z a ⊆ euclideanBall z b := euclideanBall_mono ha.le hab
  have hbU : euclideanBall z b ⊆ euclideanBall z R :=
    euclideanBall_mono (ha.trans_le hab).le hbR.le
  have hapos := volume_euclideanBall_pos z ha
  have hbpos := volume_euclideanBall_pos z (ha.trans_le hab)
  have hatop := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z ha.le)
  have hbtop := lt_top_iff_ne_top.mpr
    (volume_euclideanBall_ne_top z (ha.trans_le hab).le)
  have hineq (n : ℕ) :
      centeredVectorMeanL2 (euclideanBall z a) u.grad ≤
        (a / b) * centeredVectorMeanL2 (euclideanBall z b) u.grad +
          ((a / b) + Real.sqrt ((volume (euclideanBall z b)).toReal /
            (volume (euclideanBall z a)).toReal)) *
            Real.sqrt (integralAverage (euclideanBall z b)
              (fun x => vecNormSq (err n x))) := by
    have hvL2 : MemVectorL2On (euclideanBall z b) (v n).grad := fun i =>
      memLpOn_mono hbU ((v n).grad_memLp i)
    have herrL2 : MemVectorL2On (euclideanBall z b) (err n) := fun i =>
      (memLpOn_mono hbU (u.gradMemL2 i)).sub (hvL2 i)
    have hdecay : centeredVectorMeanL2 (euclideanBall z a) (v n).grad ≤
        (a / b) * centeredVectorMeanL2 (euclideanBall z b) (v n).grad := by
      rw [W1pFunction.convexApproxSmoothW1p_grad]
      exact centeredVectorMeanL2_classicalGradient_harmonic_decay hd
        (W1pFunction.contDiff_convexApproxSmoothW1p_toFun hU _ _ _ _ n) hR
        (fun x hx => euclideanCoordLaplacian_convexApproxSmoothW1p_eq_zero
          hU u hu hx hball hr n) ha hab hbR
    have hc := centeredVectorMeanL2_comparison_of_contraction hba hvL2 herrL2
      hapos hatop hbpos hbtop (div_nonneg ha.le (ha.trans_le hab).le) hdecay
    have hsum : (fun x => (v n).grad x + err n x) = u.grad := by
      funext x
      ext i
      simp [err]
    simpa only [hsum] using hc
  have herrlim : Tendsto (fun n => Real.sqrt (integralAverage (euclideanBall z b)
      (fun x => vecNormSq (err n x)))) atTop (𝓝 0) := by
    have h := tendsto_convexApproxSmoothW1p_sqrt_integralAverage_grad_sub
      hU u hbU hball hr
    simpa only [err, vecNormSq_sub_comm] using h
  have hlim : Tendsto (fun n =>
      (a / b) * centeredVectorMeanL2 (euclideanBall z b) u.grad +
        ((a / b) + Real.sqrt ((volume (euclideanBall z b)).toReal /
          (volume (euclideanBall z a)).toReal)) *
          Real.sqrt (integralAverage (euclideanBall z b)
            (fun x => vecNormSq (err n x)))) atTop
      (𝓝 ((a / b) * centeredVectorMeanL2 (euclideanBall z b) u.grad)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul herrlim) using 1
    ring_nf
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall hineq)

/-- Exact linear decay of centered weak-harmonic gradient oscillation,
including the outer equation radius. -/
theorem centeredVectorMeanL2_weakHarmonic_grad_decay [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall z R))
    (hu : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (u.grad x) (φ.grad x) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b ≤ R) :
    centeredVectorMeanL2 (euclideanBall z a) u.grad ≤
      (a / b) * centeredVectorMeanL2 (euclideanBall z b) u.grad := by
  rcases hbR.eq_or_lt with hbeq | hbR
  · rw [hbeq]
    rcases hab.eq_or_lt with haeq | haR
    · subst a
      subst b
      rw [div_self hR.ne', one_mul]
    let t : ℕ → ℝ := fun n => R - (R - a) * unitConvexApproxScale n / 2
    have hat (n : ℕ) : a ≤ t n := by
      have hs := unitConvexApproxScale_le_one n
      have hp := unitConvexApproxScale_pos n
      dsimp [t]
      nlinarith
    have htR (n : ℕ) : t n < R := by
      have hp := unitConvexApproxScale_pos n
      dsimp [t]
      nlinarith
    have htpos (n : ℕ) : 0 < t n := ha.trans_le (hat n)
    have htlim : Tendsto t atTop (𝓝 R) := by
      have h := (tendsto_const_nhds (x := R) (f := atTop)).sub
        ((tendsto_unitConvexApproxScale_zero.const_mul (R - a)).div_const 2)
      simpa only [mul_zero, zero_div, sub_zero, t] using h
    have hbound (n : ℕ) :
        centeredVectorMeanL2 (euclideanBall z a) u.grad ≤
          ((a / t n) * Real.sqrt ((volume (euclideanBall z R)).toReal /
            (volume (euclideanBall z (t n))).toReal)) *
              centeredVectorMeanL2 (euclideanBall z R) u.grad := by
      have hstrict := centeredVectorMeanL2_weakHarmonic_grad_decay_of_lt
        hd hR u hu ha (hat n) (htR n)
      have hmono := centeredVectorMeanL2_mono_set
        (euclideanBall_mono (htpos n).le (htR n).le) u.gradMemL2
        (volume_euclideanBall_pos z (htpos n))
        (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z (htpos n).le))
        (volume_euclideanBall_pos z hR)
        (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le))
      simpa only [mul_assoc] using hstrict.trans (mul_le_mul_of_nonneg_left hmono
        (div_nonneg ha.le (htpos n).le))
    have hcoef : Tendsto (fun n => (a / t n) *
        Real.sqrt ((volume (euclideanBall z R)).toReal /
          (volume (euclideanBall z (t n))).toReal)) atTop (𝓝 (a / R)) := by
      simp_rw [volume_euclideanBall_toReal_div_eq_div_pow z z (htpos _) hR]
      have hrat : Tendsto (fun n => R / t n) atTop (𝓝 (R / R)) :=
        tendsto_const_nhds.div htlim (ne_of_gt hR)
      have hdiv : Tendsto (fun n => a / t n) atTop (𝓝 (a / R)) :=
        tendsto_const_nhds.div htlim (ne_of_gt hR)
      simpa only [div_self hR.ne', one_pow, Real.sqrt_one, mul_one] using
        hdiv.mul (hrat.pow d).sqrt
    have hlim := hcoef.mul_const
      (centeredVectorMeanL2 (euclideanBall z R) u.grad)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall hbound)
  · exact centeredVectorMeanL2_weakHarmonic_grad_decay_of_lt
      hd hR u hu ha hab hbR

end

end PDE
