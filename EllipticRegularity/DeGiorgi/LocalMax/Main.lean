module

public import EllipticRegularity.DeGiorgi.LocalMax.Threshold
public import EllipticRegularity.DeGiorgi.LevelSetLimit
public import PDEFoundation.PDE.CoefficientModification
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Measure.RestrictedVolume

/-!
# The De Giorgi `L^∞` estimate for subsolutions (dimension at least three)

This module proves the `L^∞` estimate of the manuscript (Proposition 4.9) by the
level-set recursion of De Giorgi.  The recurrence, the nonlinear iteration, and
the endpoint of the iteration are the modules
`EllipticRegularity.DeGiorgi.LevelSetRecurrence` and
`EllipticRegularity.DeGiorgi.LevelSetLimit`; the smallness threshold is computed in
`EllipticRegularity.DeGiorgi.LocalMax.Threshold`.
-/

@[expose] public section

namespace PDE.DGNMLocalMax

open PDE MeasureTheory

/-- The squared `L²` norm of `u` over the ball, as a real number. -/
private theorem toReal_eLpNorm_sq_eq {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    (eLpNorm u.toFun 2 (volumeOn U)).toReal ^ 2 = ∫ x in U, u.toFun x ^ 2 := by
  have hmem : MemLp u.toFun 2 (volumeOn U) := u.memL2
  have h := hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ ∫ x in U, ‖u.toFun x‖ ^ ((2 : ENNReal).toReal) :=
    integral_nonneg fun x => by positivity
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs] at hnn ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- **`L^∞` estimate for subsolutions** (Proposition 4.9),
in the exact form of the statement `exists_localMaxPrinciple_constant`. -/
theorem exists_localMaxPrinciple_constant_full (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hc := thresholdConst_pos d
  set c := thresholdConst d with hcdef
  refine ⟨c ^ (-(1 / 2 : ℝ)) * 10 ^ ((d : ℝ) / 4), by positivity, ?_⟩
  intro Λ a hmeas hell u hsub
  have hU : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec d) 1) :=
    isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos
  have hΛ : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall (0 : Vec d) one_pos)).lam_le_Lam
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  obtain ⟨b, hEllb, hab⟩ :=
    exists_isEllipticFieldOn_coeffAEEqOn (measurableSet_euclideanBall (0 : Vec d) 1) hmeas hell
  have hsubb : IsWeakDivergenceFormH10SubharmonicOn b (euclideanBall (0 : Vec d) 1) u :=
    (hsub.of_ae_eq_coeff hab).toH10SubharmonicOn hU hEllb
  set N : ℝ := (eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))).toReal with hNdef
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set g : ℝ := (10 * Λ) ^ ((d : ℝ) / 4) with hgdef
  have hg0 : 0 < g := by positivity
  have hCg : c ^ (-(1 / 2 : ℝ)) * 10 ^ ((d : ℝ) / 4) * Λ ^ ((d : ℝ) / 4) =
      c ^ (-(1 / 2 : ℝ)) * g := by
    rw [hgdef, Real.mul_rpow (by norm_num) hΛ0.le]
    ring
  set κ : ℝ := c ^ (-(1 / 2 : ℝ)) * g * N with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  -- key: every K > κ bounds u on the half ball
  have key : ∀ K : ℝ, κ < K → ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), u.toFun x ≤ K := by
    intro K hK
    have hK0 : 0 < K := lt_of_le_of_lt hκ0 hK
    -- threshold
    have hgsq : g ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2)) = 1 := by
      rw [hgdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
      have : (d : ℝ) / 4 * ((2 : ℕ) : ℝ) + -((d : ℝ) / 2) = 0 := by push_cast; ring
      rw [this, Real.rpow_zero]
    have hcinv : (c ^ (-(1 / 2 : ℝ))) ^ 2 * c = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
      have : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by norm_num
      rw [this, Real.rpow_neg_one]
      field_simp
    have hN2 : N ^ 2 ≤ c * K ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2)) := by
      have h1 : κ ^ 2 ≤ K ^ 2 := by nlinarith
      have h2 : N ^ 2 = c * κ ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2)) := by
        have : c * κ ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2)) =
            ((c ^ (-(1 / 2 : ℝ))) ^ 2 * c) * (g ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2))) * N ^ 2 := by
          rw [hκdef]; ring
        rw [this, hcinv, hgsq]; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc.le) (by positivity)
    set Y : ℕ → ℝ := deGiorgiLevelSetEnergy u (0 : Vec d) (1 / 2) 1 0 K with hYdef
    have hY0 : Y 0 ≤ N ^ 2 := by
      rw [hYdef, deGiorgiLevelSetEnergy_zero, hNdef, toReal_eLpNorm_sq_eq]
      unfold positivePartEnergyOnEuclideanBall
      have hint : IntegrableOn (fun x => u.toFun x ^ 2) (euclideanBall (0 : Vec d) 1) := by
        have := u.memL2
        simpa only [pow_two] using integrableOn_mul_of_memL2On this this
      have hint2 : IntegrableOn (fun x => max (u.toFun x - 0) 0 ^ 2) (euclideanBall (0 : Vec d) 1) := by
        have h := (u.positivePartSubConst hU 0).memL2
        simpa only [H1Function.positivePartSubConst_toFun, sub_zero, pow_two]
          using integrableOn_mul_of_memL2On h h
      apply setIntegral_mono hint2 hint
      intro x
      simp only [sub_zero]
      rcases le_total (u.toFun x) 0 with h | h
      · rw [max_eq_right h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact sq_nonneg _
      · rw [max_eq_left h]
    have hrec := deGiorgiLevelSetEnergy_succ_le_geometric_of_h10Subharmonic
      (u := u) (x₀ := (0 : Vec d)) (a := b) (k₀ := 0) (K := K) (lam := 1) (Lam := Λ)
      (r := 1 / 2) (R := 1) hd hU (by norm_num) (by norm_num) subset_rfl hEllb
      one_pos hΛ0.le hsubb hK0
    have hthr := threshold_le hd hΛ hK0
    have hY0' : Y 0 ≤ deGiorgiBallIterationCoefficient d 1 Λ (1 / 2) 1 K ^
          (-(1 / deGiorgiBallIterationBeta d)) *
        deGiorgiBallIterationBase d ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) :=
      hY0.trans (hN2.trans hthr)
    have htend : Filter.Tendsto Y Filter.atTop (nhds 0) :=
      nonlinear_iteration_tendsto_zero_of_initial_small
        (deGiorgiBallIterationCoefficient_pos d one_pos hΛ0.le (by norm_num) hK0)
        (deGiorgiBallIterationBase_one_lt d) (deGiorgiBallIterationBeta_pos hd) hY0'
        (fun n => deGiorgiLevelSetEnergy_nonneg _ _ _ _ _ _ _) hrec
    have := ae_le_add_of_tendsto_deGiorgiLevelSetEnergy_zero (u := u) (x₀ := (0 : Vec d))
      (r := 1 / 2) (R := 1) (k₀ := 0) (K := K) hU (by norm_num) (by norm_num) subset_rfl hK0 htend
    simpa only [zero_add] using this
  -- pass to κ
  have hae : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)), u.toFun x ≤ κ := by
    have hall : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (1 / 2)),
        ∀ n : ℕ, u.toFun x ≤ κ + 1 / ((n : ℝ) + 1) :=
      ae_all_iff.2 fun n => key _ (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
    filter_upwards [hall] with x hx
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (hx n).trans (by linarith)
  have hess : essSup (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤ ENNReal.ofReal κ := by
    exact essSup_le_of_ae_le _ (by
      filter_upwards [hae] with x hx
      exact ENNReal.ofReal_le_ofReal hx)
  refine hess.trans (le_of_eq ?_)
  have hfin : eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ ⊤ := u.memL2.eLpNorm_ne_top
  calc ENNReal.ofReal κ = ENNReal.ofReal (c ^ (-(1 / 2 : ℝ)) * g) * ENNReal.ofReal N := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = _ := by rw [hCg, hNdef, ENNReal.ofReal_toReal hfin]

end PDE.DGNMLocalMax
