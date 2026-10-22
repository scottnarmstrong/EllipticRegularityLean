module

public import EllipticRegularity.DeGiorgi.LogPackage.SmallSupport
public import EllipticRegularity.DeGiorgi.LogPackage.MeanZeroSet
public import EllipticRegularity.DeGiorgi.LogPackage.SobolevPoincareBall

/-!
# Poincare inequality for functions vanishing on a set of positive density

Manuscript: Proposition 4.11, Step 3.
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- The `L²` norm on `B_ρ` of `w` is controlled by `|{w ≠ 0}|^{1/d}` times the gradient norm
(manuscript: (4.52)). -/
theorem smallSupport_sq_le {d : ℕ} (hd : 3 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 → ∀ {a : ℝ}, 0 < a → a ≤ 2 / 3 →
      ∀ (w : H1Function (euclideanBall (0 : Vec d) 1)) (t : Set (Vec d)), MeasurableSet t →
      (∀ x ∈ euclideanBall (0 : Vec d) ρ, x ∉ t → w.toFun x = 0) →
      volume (t ∩ euclideanBall (0 : Vec d) ρ) ≤
        ENNReal.ofReal a * volume (euclideanBall (0 : Vec d) ρ) →
      ∫ x in euclideanBall (0 : Vec d) ρ, w.toFun x ^ 2 ≤
        K ^ 2 * a ^ (2 / (d : ℝ)) *
          ∫ x in euclideanBall (0 : Vec d) ρ, vecNormSq (w.grad x) := by
  obtain ⟨K1, hK1, hSP⟩ := sobolevPoincare_two_ball hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set K2 : ℝ := Real.sqrt 3 * 2 ^ (d + 1) with hK2
  have hK2pos : 0 < K2 := by positivity
  refine ⟨K1 + K2, by positivity, ?_⟩
  intro ρ hρ hρ1 a ha ha23 w t ht hzero htV
  set V := euclideanBall (0 : Vec d) ρ with hV
  have hVsub : V ⊆ euclideanBall (0 : Vec d) 1 := euclideanBall_mono hρ.le hρ1
  have hVmeas : MeasurableSet V := measurableSet_euclideanBall _ _
  have hVpos : 0 < volume V := volume_euclideanBall_pos _ hρ
  have hVfin : volume V < ⊤ := (volume_euclideanBall_ne_top _ hρ.le).lt_top
  have hVr : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVfin.ne
  have hνmono : volumeOn V ≤ volumeOn (euclideanBall (0 : Vec d) 1) :=
    Measure.restrict_mono hVsub le_rfl
  have hwL2 : MemLp w.toFun 2 (volumeOn V) := w.memL2.mono_measure hνmono
  have hgL2 : MemLp (fun x => vecEuclideanNorm (w.grad x)) 2 (volumeOn V) :=
    w.gradMemL2.memLp_vecEuclideanNorm.mono_measure hνmono
  set m := integralAverage V w.toFun with hm
  set G := ∫ x in V, vecNormSq (w.grad x) with hG
  set Gn := euclideanFieldELpNormOn V 2 w.grad with hGn
  have hGnfin : Gn ≠ ⊤ := by
    simpa only [hGn, euclideanFieldELpNormOn, eLpNormOn] using hgL2.eLpNorm_ne_top
  have hGnsq : Gn.toReal ^ 2 = G := by
    simpa only [hGn, euclideanFieldELpNormOn, eLpNormOn, volumeOn, vecEuclideanNorm_sq]
      using toReal_eLpNorm_two_sq_eq_integral_sq hgL2
  have hw2 : (eLpNorm w.toFun 2 (volumeOn V)).toReal ^ 2 = ∫ x in V, w.toFun x ^ 2 := by
    simpa only [volumeOn] using toReal_eLpNorm_two_sq_eq_integral_sq hwL2
  -- the mean
  have hmean := mean_sq_mul_volume_le hVmeas ht hVfin hwL2 hzero
    (htV.trans (by gcongr))
  have hPoin := centeredPoincare_sq_on_boundedConvexSubdomain w
    (isOpenBoundedConvexDomain_euclideanBall 0 hρ) hVsub
    (hasEuclideanDiameterLE_euclideanBall 0 hρ) (by positivity)
    ⟨0, center_mem_euclideanBall 0 hρ⟩
  have hPle : ((2 : ℝ) ^ d * (2 * ρ)) ^ 2 ≤ ((2 : ℝ) ^ (d + 1)) ^ 2 := by
    have : (2 : ℝ) ^ d * (2 * ρ) ≤ (2 : ℝ) ^ (d + 1) := by
      rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) d]
    exact pow_le_pow_left₀ (by positivity) this 2
  have hK2sq : K2 ^ 2 = 3 * ((2 : ℝ) ^ (d + 1)) ^ 2 := by
    rw [hK2, mul_pow, Real.sq_sqrt (by norm_num)]
  have hmsq : m ^ 2 * (volume V).toReal ≤ (K2 * Gn.toReal) ^ 2 := by
    calc m ^ 2 * (volume V).toReal ≤ 3 * ∫ x in V, (w.toFun x - m) ^ 2 := hmean
      _ ≤ 3 * (((2 : ℝ) ^ d * (2 * ρ)) ^ 2 * G) := by gcongr
      _ ≤ 3 * (((2 : ℝ) ^ (d + 1)) ^ 2 * G) := by
          have hG0 : 0 ≤ G := by rw [← hGnsq]; positivity
          gcongr
      _ = (K2 * Gn.toReal) ^ 2 := by
          rw [mul_pow, hK2sq, hGnsq]; ring
  have hmabs : |m| ≤ K2 * Gn.toReal * (volume V).toReal ^ (-(1 / 2 : ℝ)) := by
    have hs : 0 < Real.sqrt (volume V).toReal := Real.sqrt_pos.mpr hVr
    have h1 : (|m| * Real.sqrt (volume V).toReal) ^ 2 ≤ (K2 * Gn.toReal) ^ 2 := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hVr.le]; exact hmsq
    have h2 : |m| * Real.sqrt (volume V).toReal ≤ K2 * Gn.toReal :=
      le_of_sq_le_sq h1 (by positivity)
    have h3 : (volume V).toReal ^ (-(1 / 2 : ℝ)) = (Real.sqrt (volume V).toReal)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hVr.le]
    rw [h3, ← div_eq_mul_inv, le_div_iff₀ hs]
    exact h2
  -- exponent bookkeeping
  have hQ : 2 ≤ sobolevConjugate d 2 := sobolevConjugate_two_ge hd
  have hQpos : 0 < sobolevConjugate d 2 := by linarith
  have hexpQ : -(1 / 2 : ℝ) + 1 / sobolevConjugate d 2 = -(1 / (d : ℝ)) := by
    have := one_half_sub_inv_sobolevConjugate hd
    linarith
  set Q : ENNReal := ENNReal.ofReal (sobolevConjugate d 2) with hQdef
  have hQtoReal : Q.toReal = sobolevConjugate d 2 := ENNReal.toReal_ofReal hQpos.le
  have hQ1 : 1 ≤ Q := by
    rw [hQdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- constant piece
  have hconst : eLpNorm (fun _ : Vec d => m) Q (volumeOn V) ≤
      ENNReal.ofReal K2 * Gn * volume V ^ (-(1 / (d : ℝ))) := by
    rw [eLpNorm_const m (by rw [hQdef]; simpa using hQpos) (by
      simp [volumeOn, Measure.restrict_eq_zero, hVpos.ne'])]
    rw [Measure.restrict_apply_univ, Real.enorm_eq_ofReal_abs, hQtoReal, one_div]
    have h1 : ENNReal.ofReal |m| ≤ ENNReal.ofReal K2 * Gn * volume V ^ (-(1 / 2 : ℝ)) := by
      calc ENNReal.ofReal |m|
          ≤ ENNReal.ofReal (K2 * Gn.toReal * (volume V).toReal ^ (-(1 / 2 : ℝ))) :=
            ENNReal.ofReal_le_ofReal hmabs
        _ = ENNReal.ofReal K2 * Gn * volume V ^ (-(1 / 2 : ℝ)) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hK2pos.le,
              ENNReal.ofReal_toReal hGnfin,
              ← ENNReal.ofReal_rpow_of_pos hVr, ENNReal.ofReal_toReal hVfin.ne]
    calc ENNReal.ofReal |m| * volume V ^ (sobolevConjugate d 2)⁻¹
        ≤ (ENNReal.ofReal K2 * Gn * volume V ^ (-(1 / 2 : ℝ))) *
            volume V ^ (sobolevConjugate d 2)⁻¹ := by gcongr
      _ = ENNReal.ofReal K2 * Gn * volume V ^ (-(1 / (d : ℝ))) := by
          rw [mul_assoc, ← ENNReal.rpow_add _ _ hVpos.ne' hVfin.ne, ← one_div, hexpQ]
  have hNq : eLpNorm w.toFun Q (volumeOn V) ≤
      ENNReal.ofReal (K1 + K2) * volume V ^ (-(1 / (d : ℝ))) * Gn := by
    have hsplit : w.toFun = (fun x => w.toFun x - m) + fun _ => m := by ext x; simp
    have hm1 : AEStronglyMeasurable (fun x => w.toFun x - m) (volumeOn V) :=
      hwL2.aestronglyMeasurable.sub aestronglyMeasurable_const
    calc eLpNorm w.toFun Q (volumeOn V)
        = eLpNorm ((fun x => w.toFun x - m) + fun _ => m) Q (volumeOn V) := by rw [← hsplit]
      _ ≤ eLpNorm (fun x => w.toFun x - m) Q (volumeOn V) +
            eLpNorm (fun _ : Vec d => m) Q (volumeOn V) :=
          eLpNorm_add_le hQ1
      _ ≤ ENNReal.ofReal K1 * volume V ^ (-(1 / (d : ℝ))) * Gn +
            ENNReal.ofReal K2 * Gn * volume V ^ (-(1 / (d : ℝ))) :=
          add_le_add (by simpa only [hGn, eLpNormOn, ENNReal.ofReal_ofNat] using hSP hρ hρ1 w)
            hconst
      _ = ENNReal.ofReal (K1 + K2) * volume V ^ (-(1 / (d : ℝ))) * Gn := by
          rw [ENNReal.ofReal_add hK1.le hK2pos.le]; ring
  have hzero' : ∀ᵐ x ∂(volumeOn V), x ∉ t → w.toFun x = 0 :=
    (ae_restrict_iff' hVmeas).mpr (Filter.Eventually.of_forall fun x hx => hzero x hx)
  have hH := eLpNorm_two_le_of_ae_zero_off hd ht hwL2.aestronglyMeasurable hzero'
  have hN2 : eLpNorm w.toFun 2 (volumeOn V) ≤
      ENNReal.ofReal ((K1 + K2) * a ^ (1 / (d : ℝ)) * Gn.toReal) := by
    calc eLpNorm w.toFun 2 (volumeOn V)
        ≤ eLpNorm w.toFun Q (volumeOn V) * volume (t ∩ V) ^ (1 / (d : ℝ)) := hH
      _ ≤ (ENNReal.ofReal (K1 + K2) * volume V ^ (-(1 / (d : ℝ))) * Gn) *
            (ENNReal.ofReal a * volume V) ^ (1 / (d : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (K1 + K2) * Gn * ENNReal.ofReal a ^ (1 / (d : ℝ)) *
            (volume V ^ (-(1 / (d : ℝ))) * volume V ^ (1 / (d : ℝ))) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]; ring
      _ = ENNReal.ofReal ((K1 + K2) * a ^ (1 / (d : ℝ)) * Gn.toReal) := by
          rw [← ENNReal.rpow_add _ _ hVpos.ne' hVfin.ne, neg_add_cancel, ENNReal.rpow_zero,
            mul_one, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_toReal hGnfin, ENNReal.ofReal_rpow_of_pos ha]
          ring
  have hN2r : (eLpNorm w.toFun 2 (volumeOn V)).toReal ≤ (K1 + K2) * a ^ (1 / (d : ℝ)) * Gn.toReal :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hN2
  rw [← hw2]
  calc (eLpNorm w.toFun 2 (volumeOn V)).toReal ^ 2
      ≤ ((K1 + K2) * a ^ (1 / (d : ℝ)) * Gn.toReal) ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg hN2r 2
    _ = (K1 + K2) ^ 2 * a ^ (2 / (d : ℝ)) * G := by
        have h : (a ^ (1 / (d : ℝ))) ^ 2 = a ^ (2 / (d : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
          congr 1
          push_cast; ring
        rw [mul_pow, mul_pow, hGnsq, h]
