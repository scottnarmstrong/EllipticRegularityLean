module

public import EllipticRegularity.Parabolic.Cauchy.Energy.GlobalIdentity
public import EllipticRegularity.Parabolic.Cauchy.Energy.InitialTrace
public import EllipticRegularity.Parabolic.Energy.Bridge
public import EllipticRegularity.Parabolic.Caccioppoli.Assembly
public import EllipticRegularity.Parabolic.Chain.ScaleLimit
public import EllipticRegularity.Parabolic.Chain.H1Solution
public import PDEFoundation.Sobolev.W1p.Truncation
public import EllipticRegularity.Ch4.GreenDecay.Helpers
public import Mathlib.Analysis.Calculus.MeanValue
public import EllipticRegularity.Parabolic.Cauchy.Energy.PositivityIdentity

/-! # Positivity of whole-space Cauchy energy solutions -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set Filter Topology intervalIntegral

theorem cauchyNegativeEnergy_slice_ae_zero {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x)
    (ε : ℝ) (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    ∀ᵐ x : Vec d, cauchyNegativeEnergy ε (u.toFun (x, t)) = 0 := by
  let Kn : ℕ → Set (Vec d) := fun n => euclideanClosedBall 0 ((n : ℝ) + 1)
  have hKnCompact (n : ℕ) : IsCompact (Kn n) :=
    isCompact_euclideanClosedBall 0 (by positivity)
  have hKnMeas (n : ℕ) : MeasurableSet (Kn n) :=
    measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
  have hBallIntegralZero (n : ℕ) :
      ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) = 0 := by
    have hFnInt := cauchyNegativeEnergy_slice_integrableOn u ε hε ht (hKnCompact n)
    have hFnNonneg : ∀ᵐ x ∂(volume.restrict (Kn n)),
        0 ≤ cauchyNegativeEnergy ε (u.toFun (x, t)) :=
      ae_of_all _ fun x => cauchyNegativeEnergy_nonneg ε hε _
    have hA_nonneg : 0 ≤ ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) :=
      setIntegral_nonneg_of_ae_restrict hFnNonneg
    by_contra hAne
    have hApos : 0 < ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) :=
      lt_of_le_of_ne hA_nonneg (Ne.symm hAne)
    let Qmax : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
    let M : ℝ := ∫ z in Qmax, cauchyFluxMajorant a u z
    have hMInt : IntegrableOn (cauchyFluxMajorant a u) Qmax := by
      simpa only [Qmax] using cauchyFluxMajorant_integrable_Ioc ha u ⟨hsT.le, le_rfl⟩
    have hMNonneg : 0 ≤ M := by
      dsimp [M]
      apply MeasureTheory.integral_nonneg_of_ae
      refine ae_of_all _ fun z => ?_
      apply mul_nonneg (abs_nonneg _)
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    obtain ⟨R, hRbig⟩ := exists_gt (max ((n : ℝ) + 1) (32 * M /
      (∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)))))
    have hRinner : (n : ℝ) + 1 < R := (le_max_left _ _).trans_lt hRbig
    have hRpos : 0 < R := by
      linarith [hRinner]
    have hRratio : 32 * M / (∫ x in Kn n,
        cauchyNegativeEnergy ε (u.toFun (x, t))) < R := (le_max_right _ _).trans_lt hRbig
    let ξ : Vec d → ℝ := (cauchySpatialCutoff R hRpos).toFun
    let Kouter : Set (Vec d) := euclideanClosedBall 0 (2 * R)
    have hKouterCompact : IsCompact Kouter :=
      isCompact_euclideanClosedBall 0 (by positivity)
    have hFouter : IntegrableOn (fun x : Vec d =>
        cauchyNegativeEnergy ε (u.toFun (x, t))) Kouter :=
      cauchyNegativeEnergy_slice_integrableOn u ε hε ht hKouterCompact
    have hξMeas : AEStronglyMeasurable ξ (volume.restrict Kouter) := by
      dsimp [ξ]
      exact (cauchySpatialCutoff R hRpos).smooth.continuous.aestronglyMeasurable
    have hξBound : ∀ᵐ x ∂(volume.restrict Kouter), ‖ξ x‖ ≤ 1 := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by
        have := (cauchySpatialCutoff R hRpos).nonneg x
        linarith,
        (cauchySpatialCutoff R hRpos).le_one x⟩
    have hproductInt : IntegrableOn (fun x : Vec d =>
        ξ x * cauchyNegativeEnergy ε (u.toFun (x, t))) Kouter := by
      have hmul := hFouter.bdd_mul hξMeas (c := 1) hξBound
      change Integrable (fun x => ξ x * cauchyNegativeEnergy ε (u.toFun (x, t)))
        (volume.restrict Kouter)
      simpa only [mul_comm] using hmul
    have hproductNonneg : ∀ᵐ x ∂(volume.restrict Kouter),
        0 ≤ ξ x * cauchyNegativeEnergy ε (u.toFun (x, t)) := by
      filter_upwards [] with x
      exact mul_nonneg ((cauchySpatialCutoff R hRpos).nonneg x)
        (cauchyNegativeEnergy_nonneg ε hε _)
    have hKnSub : Kn n ⊆ Kouter := by
      dsimp [Kn, Kouter]
      apply euclideanClosedBall_mono (by positivity)
      nlinarith
    have hinnerCut : ∀ x ∈ Kn n, ξ x = 1 := by
      intro x hx
      have hxnorm : vecEuclideanNorm x ≤ (n : ℝ) + 1 := by
        have h := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hx
        simpa only [sub_zero] using h
      have hxball : x ∈ euclideanBall 0 R := by
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).2
        simpa only [sub_zero] using lt_of_le_of_lt hxnorm hRinner
      exact (cauchySpatialCutoff R hRpos).eq_one_on_inner x hxball
    have hinnerEq :
        (∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t))) =
          ∫ x in Kn n, ξ x * cauchyNegativeEnergy ε (u.toFun (x, t)) := by
      apply setIntegral_congr_ae (hKnMeas n)
      filter_upwards [] with x hx
      rw [hinnerCut x hx]
      ring
    have hproductMono :
        (∫ x in Kn n, ξ x * cauchyNegativeEnergy ε (u.toFun (x, t))) ≤
          ∫ x in Kouter, ξ x * cauchyNegativeEnergy ε (u.toFun (x, t)) :=
      setIntegral_mono_set hproductInt hproductNonneg
        (ae_of_all _ fun x hx => hKnSub hx)
    have hmomentEq :
        (∫ x in Kouter, ξ x * cauchyNegativeEnergy ε (u.toFun (x, t))) =
          cauchyNegativeMoment ε R hRpos u t := by rfl
    have hAupper :
        (∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t))) ≤
          cauchyNegativeMoment ε R hRpos u t := by
      calc
        _ = ∫ x in Kn n, ξ x * cauchyNegativeEnergy ε (u.toFun (x, t)) := hinnerEq
        _ ≤ ∫ x in Kouter, ξ x * cauchyNegativeEnergy ε (u.toFun (x, t)) := hproductMono
        _ = cauchyNegativeMoment ε R hRpos u t := hmomentEq
    have hmomentBound := cauchyNegativeMoment_upper_bound hsT ha f hf u hu hf0
      ε R hε hRpos ht hst
    have hmul : 32 * M < R *
        (∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t))) := by
      have h := mul_lt_mul_of_pos_right hRratio hApos
      have hdiv : (32 * M /
          (∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)))) *
          (∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t))) = 32 * M := by
        field_simp [ne_of_gt hApos]
      nlinarith
    have hsmall : (32 / R) * M <
        ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) := by
      have hdiv : (32 * M) / R <
          ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) :=
        (div_lt_iff₀ hRpos).2 (by nlinarith [hmul])
      have heq : (32 / R) * M = (32 * M) / R := by
        field_simp [ne_of_gt hRpos]
      rw [heq]
      exact hdiv
    have hcontr : ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) <
        ∫ x in Kn n, cauchyNegativeEnergy ε (u.toFun (x, t)) := by
      calc
        _ ≤ cauchyNegativeMoment ε R hRpos u t := hAupper
        _ ≤ (32 / R) * M := by simpa only [M, Qmax] using hmomentBound
        _ < _ := hsmall
    exact (lt_irrefl _ hcontr)
  have hBallZero (n : ℕ) : ∀ᵐ x ∂(volume.restrict (Kn n)),
      cauchyNegativeEnergy ε (u.toFun (x, t)) = 0 := by
    have hFnInt := cauchyNegativeEnergy_slice_integrableOn u ε hε ht (hKnCompact n)
    have hFnNonneg : ∀ᵐ x ∂(volume.restrict (Kn n)),
        0 ≤ cauchyNegativeEnergy ε (u.toFun (x, t)) :=
      ae_of_all _ fun x => cauchyNegativeEnergy_nonneg ε hε _
    exact (integral_eq_zero_iff_of_nonneg_ae hFnNonneg hFnInt).mp (hBallIntegralZero n)
  have hBallZero' (n : ℕ) : ∀ᵐ x ∂volume,
      x ∈ Kn n → cauchyNegativeEnergy ε (u.toFun (x, t)) = 0 :=
    (ae_restrict_iff' (hKnMeas n)).1 (hBallZero n)
  have hall : ∀ᵐ x : Vec d, ∀ n, x ∈ Kn n →
      cauchyNegativeEnergy ε (u.toFun (x, t)) = 0 := by
    rw [ae_all_iff]
    exact hBallZero'
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (vecEuclideanNorm x)
  have hxnorm : vecEuclideanNorm (x - (0 : Vec d)) ≤ (n : ℝ) + 1 := by
    rw [sub_zero]
    linarith
  have hxball : x ∈ Kn n := by
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact hxnorm
  exact hx n hxball

/-- Nonnegative Cauchy data give nonnegative values on every time slice. -/
theorem cauchyPositivity (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (s T : ℝ)
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (t : ℝ) (ht : t ∈ Icc s T) :
    ∀ᵐ x : Vec d, 0 ≤ u.toFun (x, t) := by
  by_cases hst : s < t
  · have hzero : ∀ᵐ x : Vec d, ∀ n : ℕ,
        cauchyNegativeEnergy (1 / ((n : ℝ) + 1)) (u.toFun (x, t)) = 0 := by
      rw [ae_all_iff]
      intro n
      have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      exact cauchyNegativeEnergy_slice_ae_zero hsT ha f hf u hu hf0
        (1 / ((n : ℝ) + 1)) hε ht hst
    filter_upwards [hzero] with x hx
    by_contra hnot
    have huNeg : u.toFun (x, t) < 0 := lt_of_not_ge hnot
    have hden : 0 < -u.toFun (x, t) := neg_pos.mpr huNeg
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / (-u.toFun (x, t)))
    have hmul : 2 < (-u.toFun (x, t)) * ((n : ℝ) + 1) := by
      have hmul' := (div_lt_iff₀ hden).mp hn
      nlinarith [hden, hmul']
    have hsmall : 2 / ((n : ℝ) + 1) < -u.toFun (x, t) :=
      (div_lt_iff₀ (by positivity)).2 (by nlinarith [hmul])
    have hle : u.toFun (x, t) ≤ -2 * (1 / ((n : ℝ) + 1)) := by
      have hEq : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
      rw [hEq] at hsmall
      linarith
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hpositive := cauchyNegativeEnergy_pos_of_le
      (1 / ((n : ℝ) + 1)) hε hle
    rw [hx n] at hpositive
    exact (lt_irrefl 0) hpositive
  · have hts : t = s := by
      apply le_antisymm
      · exact le_of_not_gt hst
      · exact ht.1
    subst t
    exact cauchy_initial_slice_nonneg a s T f u hu hf0


end PDE.Parabolic.Cauchy.Energy
