module

public import EllipticRegularity.Ch4.GreenFunction.Setting
public import SobolevStatements.Sobolev
public import PDEFoundation.Sobolev.Ch4.H10Algebra
public import PDEFoundation.Sobolev.Ch4.H10ToW1p

/-!
# Level sets of the approximate Green functions (Step 5 of Proposition 4.40, first half)

Testing the equation of `Gₙ` with `w_t = min(Gₙ, t) ∈ H¹₀(B_R)` gives `‖∇ w_t‖₂² ≤ t`; the
Sobolev inequality then gives `|{Gₙ ≥ t}| ≤ A t^{-d/(d-2)}` with `A = A(d)` independent of
`Λ`, `R` and `n`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- An average of a function bounded above by `c` is at most `c`. -/
theorem integralAverage_le_of_le {f : Vec d → ℝ} {S : Set (Vec d)} (hS : MeasurableSet S)
    (h0 : volume S ≠ 0) (hfin : volume S ≠ ⊤) (hf : IntegrableOn f S) {c : ℝ}
    (hc : ∀ x ∈ S, f x ≤ c) : integralAverage S f ≤ c := by
  have hpos : 0 < (volume S).toReal := ENNReal.toReal_pos h0 hfin
  have hle : ∫ x in S, f x ≤ ∫ x in S, c :=
    setIntegral_mono_on hf (integrableOn_const hfin) hS hc
  rw [setIntegral_const, smul_eq_mul, Measure.real] at hle
  rw [integralAverage, inv_mul_le_iff₀ hpos]
  linarith

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

theorem volume_ball_ne_top (S : ApproxSetting d Λ R a) :
    volume (euclideanBall (0 : Vec d) R) ≠ ⊤ :=
  volume_euclideanBall_ne_top _ S.hR.le

/-- **Truncated energy**: `∫ |∇ min(Gₙ, t)|² ≤ t`. -/
theorem integral_vecNormSq_min_le (S : ApproxSetting d Λ R a) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in euclideanBall (0 : Vec d) R, vecNormSq
      ((Ch4Infra.minH10 (isOpen_euclideanBall _ _) S.volume_ball_ne_top (S.G n)
          ht).toH1Function.grad x)
      ≤ t := by
  set B := euclideanBall (0 : Vec d) R
  set w := Ch4Infra.minH10 (isOpen_euclideanBall _ _) S.volume_ball_ne_top (S.G n) ht
  have hB : MeasurableSet B := measurableSet_euclideanBall _ _
  obtain ⟨htest, heq⟩ := S.solG n w
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at heq
  rw [integral_approxSource_mul (approxRadius_lt S.hR n).le (approxRadius_pos S.hR n).le] at heq
  have hwfun := Ch4Infra.minH10_toFun (isOpen_euclideanBall _ _) S.volume_ball_ne_top (S.G n) ht
  have hwgrad := Ch4Infra.minH10_grad (isOpen_euclideanBall _ _) S.volume_ball_ne_top (S.G n) ht
  -- the average of `min (Gₙ, t)` is at most `t`
  have havg : integralAverage (euclideanBall (0 : Vec d) (approxRadius R n))
      w.toH1Function.toFun ≤ t := by
    have := isFiniteMeasure_volumeOn_euclideanBall (0 : Vec d) S.hR.le
    have hint : IntegrableOn w.toH1Function.toFun B :=
      w.toH1Function.memL2.integrable one_le_two
    refine integralAverage_le_of_le (measurableSet_euclideanBall _ _)
      (volume_euclideanBall_pos _ (approxRadius_pos S.hR n)).ne'
      (volume_euclideanBall_ne_top _ (approxRadius_pos S.hR n).le)
      (hint.mono_set (euclideanBall_mono (approxRadius_pos S.hR n).le (approxRadius_lt S.hR n).le))
      fun x _ => ?_
    rw [hwfun]
    exact min_le_right _ _
  refine le_trans ?_ (heq.le.trans havg)
  refine setIntegral_mono_on (integrableOn_vecNormSq_of_memVectorL2On w.toH1Function.gradMemL2)
    htest.flux_integrable hB fun x hx => ?_
  rw [hwgrad]
  by_cases hxt : (S.G n).toH1Function.toFun x ≤ t
  · have hmem : x ∈ {y | (S.G n).toH1Function.toFun y ≤ t} := hxt
    simp only [Set.indicator_of_mem hmem]
    have := (S.hell x hx).coercive ((S.G n).toH1Function.grad x)
    rw [one_mul] at this
    rw [vecDot_comm]
    exact this
  · have hmem : x ∉ {y | (S.G n).toH1Function.toFun y ≤ t} := hxt
    simp only [Set.indicator_of_notMem hmem]
    simp [vecNormSq]

end ApproxSetting

/-- The Chebyshev–Sobolev algebra: from `tᵠ X ≤ (K √t)ᵠ` deduce `X ≤ Kᵠ t^{-q/2}`. -/
theorem le_of_mul_rpow_le {X : ℝ≥0∞} {t K q : ℝ} (ht : 0 < t) (hK : 0 ≤ K) (hq : 0 < q)
    (h : ENNReal.ofReal t ^ q * X ≤ ENNReal.ofReal (K * Real.sqrt t) ^ q) :
    X ≤ ENNReal.ofReal (K ^ q * t ^ (-(q / 2))) := by
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  rw [ENNReal.ofReal_rpow_of_nonneg ht.le hq.le,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hq.le, mul_comm] at h
  have h' := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 htq).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2 h
  rw [← ENNReal.ofReal_div_of_pos htq] at h'
  refine h'.trans (le_of_eq ?_)
  congr 1
  rw [Real.mul_rpow hK (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le,
    mul_div_assoc, ← Real.rpow_sub ht]
  congr 2
  ring

/-- **Level-set bound** for the approximate Green functions, with `A = A(d)`. -/
theorem volume_level_le (hd : 3 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Λ R : ℝ} {a : CoeffField d} (S : ApproxSetting d Λ R a) (n : ℕ)
      (t : ℝ), 0 < t →
      volume {x | x ∈ euclideanBall (0 : Vec d) R ∧ t ≤ (S.G n).toH1Function.toFun x} ≤
        ENNReal.ofReal (A * t ^ (-((d : ℝ) / ((d : ℝ) - 2)))) := by
  obtain ⟨CS, hCS, hSob⟩ := exists_sobolev_constant d (by omega)
  have hd2 : (2 : ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  set q := sobolevConjugate d 2 with hq
  have hqpos : 0 < q := by
    rw [hq, sobolevConjugate]
    exact div_pos (by positivity) (by linarith)
  have hq2 : q / 2 = (d : ℝ) / ((d : ℝ) - 2) := by
    rw [hq, sobolevConjugate]
    field_simp
  set K := CS * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) with hK
  have hKpos : 0 < K := mul_pos hCS (div_pos (by linarith) (by linarith))
  refine ⟨K ^ q, Real.rpow_pos_of_pos hKpos q, ?_⟩
  intro Λ R a S n t ht
  set B := euclideanBall (0 : Vec d) R
  have hBo : IsOpen B := isOpen_euclideanBall _ _
  have hfin := S.volume_ball_ne_top
  set w := Ch4Infra.minH10 hBo hfin (S.G n) ht.le
  have hwfun := Ch4Infra.minH10_toFun hBo hfin (S.G n) ht.le
  have hp2 : ENNReal.ofReal 2 ≤ 2 := by simp
  have hp1 : 1 ≤ ENNReal.ofReal 2 := by simp
  set u := Ch4Infra.h1ToW1p hfin hp2 w.toH1Function
  have hu : u.HasSupportedSmoothApproximation :=
    ⟨Ch4Infra.h10SupportedSmoothApproximationW1p hfin hp1 hp2 w⟩
  have hS := (hSob 2 (by norm_num) hd2).2 B hBo u hu
  -- the gradient bound
  have hgradL2 : MemLp (fun x => vecEuclideanNorm (w.toH1Function.grad x)) 2 (volumeOn B) :=
    GradMemLpOn.memLp_vecEuclideanNorm w.toH1Function.gradMemL2
  have hgrad : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal 2) (volumeOn B) ≤
      ENNReal.ofReal (Real.sqrt t) := by
    change eLpNorm (fun x => vecEuclideanNorm (w.toH1Function.grad x)) (ENNReal.ofReal 2)
      (volumeOn B) ≤ _
    rw [ENNReal.ofReal_ofNat, ← ENNReal.ofReal_toReal hgradL2.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.le_sqrt ENNReal.toReal_nonneg ht.le, toReal_eLpNorm_two_sq_eq_integral_sq hgradL2]
    refine le_trans (le_of_eq ?_) (S.integral_vecNormSq_min_le n ht.le)
    congr 1
    funext x
    rw [vecEuclideanNorm_sq]
  have hSob' : eLpNorm w.toH1Function.toFun (ENNReal.ofReal q) (volumeOn B) ≤
      ENNReal.ofReal (K * Real.sqrt t) := by
    refine hS.trans ?_
    rw [ENNReal.ofReal_mul hKpos.le]
    exact mul_le_mul_right hgrad _
  -- Chebyshev
  have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := volumeOn B) (f := w.toH1Function.toFun)
    (p := ENNReal.ofReal q) (by simpa using hqpos) ENNReal.ofReal_ne_top (ENNReal.ofReal t)
  rw [ENNReal.toReal_ofReal hqpos.le] at hcheb
  have hsub : volume {x | x ∈ B ∧ t ≤ (S.G n).toH1Function.toFun x} ≤
      volumeOn B {x | ENNReal.ofReal t ≤ ‖w.toH1Function.toFun x‖ₑ} := by
    refine le_trans (measure_mono ?_) (Measure.le_restrict_apply _ _)
    intro x ⟨hxB, hxt⟩
    refine ⟨?_, hxB⟩
    change ENNReal.ofReal t ≤ ‖w.toH1Function.toFun x‖ₑ
    rw [hwfun]
    simp only [min_eq_right hxt, Real.enorm_eq_ofReal_abs, abs_of_pos ht, le_refl]
  have hfinal := le_of_mul_rpow_le ht hKpos.le hqpos
    (hcheb.trans (ENNReal.rpow_le_rpow hSob' hqpos.le))
  rw [hq2] at hfinal
  exact hsub.trans hfinal

end PDE.Ch4Green
