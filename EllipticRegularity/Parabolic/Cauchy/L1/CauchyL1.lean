/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Positivity
public import EllipticRegularity.Parabolic.Cauchy.L1.Entropy
public import EllipticRegularity.Parabolic.Chain.H1Solution
public import EllipticRegularity.Ch4.GreenDecay.Helpers
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Whole-space L¹ contraction -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.L1

open MeasureTheory Set Filter Topology

noncomputable def cauchyAbsMoment {d : ℕ} {s T : ℝ}
    (δ R : ℝ) (hR : 0 < R)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (τ : ℝ) : ℝ :=
  ∫ x in euclideanClosedBall 0 (2 * R),
    (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
      cauchyAbsEntropy δ (u.toFun (x, τ))

private noncomputable def cauchyAbsRemainder {d : ℕ} {s T : ℝ}
    (a : ParCoeffField d) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (δ R : ℝ) (hR : 0 < R) (z : Vec d × ℝ) : ℝ :=
  deriv (deriv (cauchyAbsEntropy δ)) (u.toFun z) *
      (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z *
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z +
    deriv (cauchyAbsEntropy δ) (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z))
        (parSpaceGrad (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z)

private theorem cauchyL1_slice_norm_continuousOn {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) :
    ContinuousOn (fun τ => ∫ x : Vec d, u.toFun (x, τ) ^ 2) (Icc s T) := by
  have hq := PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable ha u
  have hqFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hq
  let qbar : ℝ → ℝ := fun τ => ∫ x : Vec d,
    PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u (x, τ)
  have hqbarInt : IntegrableOn qbar (Icc s T) := by
    simpa only [qbar, setIntegral_univ] using hqFubini.1
  have hprimitive : ContinuousOn (fun τ => ∫ r in Ioc s τ, qbar r) (Icc s T) :=
    intervalIntegral.continuousOn_primitive hqbarInt
  have hbulkEq (τ : ℝ) (hτ : τ ∈ Icc s T) :
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s τ,
        PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z =
        ∫ r in Ioc s τ, qbar r := by
    have hsub : (univ : Set (Vec d)) ×ˢ Ioc s τ ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T :=
      prod_mono subset_rfl (fun r hr => ⟨hr.1.le, hr.2.trans hτ.2⟩)
    have hFub := PDE.Parabolic.WeakSlice.integral_prod_slices (hq.mono_set hsub)
    simpa only [qbar, setIntegral_univ] using hFub.2
  have hformula : ContinuousOn (fun τ => (∫ x : Vec d, f x ^ 2) -
      2 * ∫ r in Ioc s τ, qbar r) (Icc s T) :=
    continuousOn_const.sub (hprimitive.const_mul 2)
  refine hformula.congr ?_
  intro τ hτ
  have hId := PDE.Parabolic.Cauchy.Energy.cauchy_energy_identity_real hsT ha f hf u hu hτ
  rw [hbulkEq τ hτ] at hId
  linarith

private theorem cauchyL1_local_square_tendsto {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {R : ℝ} (hR : 0 ≤ R)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc s T) :
    Tendsto (fun τ => ∫ x in euclideanClosedBall (0 : Vec d) R,
      (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) (𝓝[Icc s T] t₀) (𝓝 0) := by
  let K : ℕ → Set (Vec d) := fun n => euclideanClosedBall 0 ((n : ℝ) + 1)
  have hcover : AECover volume atTop K := by
    constructor
    · filter_upwards [] with x
      obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hnorm : vecEuclideanNorm (x - (0 : Vec d)) ≤ (n : ℝ) + 1 := by
        rw [sub_zero]
        linarith
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 hnorm
    · intro n
      exact measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
  have hu₀sq : Integrable (fun x : Vec d => u.toFun (x, t₀) ^ 2) volume :=
    PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable hsT ha f hf u hu ht₀
  let E₀ : ℝ := ∫ x : Vec d, u.toFun (x, t₀) ^ 2
  have htail : Tendsto (fun n : ℕ => E₀ -
      ∫ x in K n, u.toFun (x, t₀) ^ 2) atTop (𝓝 0) := by
    have hK := hcover.integral_tendsto_of_countably_generated hu₀sq
    have hconst : Tendsto (fun _ : ℕ => E₀) atTop (𝓝 E₀) := tendsto_const_nhds
    simpa only [E₀, sub_self] using hconst.sub hK
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop,
      E₀ - ∫ x in K n, u.toFun (x, t₀) ^ 2 < ε / 3 :=
    htail.eventually (Iio_mem_nhds (by linarith))
  have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt R
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨n, hnsmall, hnlarge⟩ := (hsmall.and hlarge).exists
  let Kn := K n
  have hKcompact : IsCompact Kn := isCompact_euclideanClosedBall 0 (by positivity)
  have hKmeas : MeasurableSet Kn := measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
  have hK0sub : euclideanClosedBall (0 : Vec d) R ⊆ Kn :=
    euclideanClosedBall_mono hR hnlarge
  let ψ : Vec d → ℝ := Kn.indicator (fun x => u.toFun (x, t₀))
  have hψLp : MemLp ψ 2 volume := by
    rw [memLp_indicator_iff_restrict hKmeas]
    exact u.sliceL2loc t₀ ht₀ Kn hKcompact (subset_univ _)
  have hψc : IsL2c (univ : Set (Vec d)) ψ := by
    refine ⟨?_, Kn, hKcompact, subset_univ _, ?_⟩
    · simpa [PDE.MemL2On, PDE.MemLpOn, PDE.volumeOn] using hψLp
    · intro x hx
      simp [ψ, hx]
  have hpairCont := u.weakCont ψ hψc
  let E : ℝ → ℝ := fun τ => ∫ x : Vec d, u.toFun (x, τ) ^ 2
  let P : ℝ → ℝ := fun τ => ∫ x : Vec d, u.toFun (x, τ) * ψ x
  let B : ℝ → ℝ := fun τ => E τ + (∫ x in Kn, u.toFun (x, t₀) ^ 2) - 2 * P τ
  have hEcont : ContinuousOn E (Icc s T) := by
    simpa only [E] using cauchyL1_slice_norm_continuousOn hsT ha f hf u hu
  have hPcont : ContinuousOn P (Icc s T) := by simpa only [P, setIntegral_univ] using hpairCont
  have hpair (τ : ℝ) : P τ =
      ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) := by
    calc
      P τ = ∫ x : Vec d,
          Kn.indicator (fun x => u.toFun (x, τ) * u.toFun (x, t₀)) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Kn <;> simp [ψ, hx]
      _ = ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) := integral_indicator hKmeas
  have hBcont : ContinuousOn B (Icc s T) := by
    change ContinuousOn ((fun τ => E τ + (∫ x in Kn, u.toFun (x, t₀) ^ 2)) -
      (fun τ => 2 * P τ)) (Icc s T)
    exact (hEcont.add continuousOn_const).sub (hPcont.const_mul 2)
  have hB₀ : B t₀ = E₀ - ∫ x in Kn, u.toFun (x, t₀) ^ 2 := by
    change (E t₀ + ∫ x in Kn, u.toFun (x, t₀) ^ 2) - 2 * P t₀ = _
    rw [hpair t₀]
    simp only [E, E₀]
    ring_nf
  have hB₀small : B t₀ < ε / 3 := by simpa [hB₀, Kn, E₀] using hnsmall
  have hB_event : ∀ᶠ τ in 𝓝[Icc s T] t₀, B τ < ε :=
    (hBcont t₀ ht₀).eventually (Iio_mem_nhds (by linarith))
  have hErr_nonneg (τ : ℝ) : 0 ≤ ∫ x in euclideanClosedBall (0 : Vec d) R,
      (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 :=
    setIntegral_nonneg (measurableSet_euclideanClosedBall _ _) fun _ _ => sq_nonneg _
  have hcompare : ∀ τ ∈ Icc s T,
      (∫ x in euclideanClosedBall (0 : Vec d) R,
        (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) ≤ B τ := by
    intro τ hτ
    have hUτ := u.sliceL2loc τ hτ Kn hKcompact (subset_univ _)
    have hU₀ := u.sliceL2loc t₀ ht₀ Kn hKcompact (subset_univ _)
    have hUτsq : IntegrableOn (fun x : Vec d => u.toFun (x, τ) ^ 2) Kn := by
      change Integrable (fun x => (parSlice u.toFun τ x) ^ 2) (volume.restrict Kn)
      simpa only [parSlice] using hUτ.integrable_sq
    have hU₀sq : IntegrableOn (fun x : Vec d => u.toFun (x, t₀) ^ 2) Kn := by
      change Integrable (fun x => (parSlice u.toFun t₀ x) ^ 2) (volume.restrict Kn)
      simpa only [parSlice] using hU₀.integrable_sq
    have hprod : IntegrableOn (fun x : Vec d => u.toFun (x, τ) * u.toFun (x, t₀)) Kn := by
      change Integrable (parSlice u.toFun τ * parSlice u.toFun t₀) (volume.restrict Kn)
      simpa only [parSlice] using hUτ.integrable_mul hU₀
    have hdiff : IntegrableOn (fun x : Vec d =>
        (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) Kn := by
      refine (hUτsq.add hU₀sq).sub (hprod.const_mul 2) |>.congr ?_
      filter_upwards [] with x
      simp only [Pi.add_apply, Pi.sub_apply, pow_two]
      ring_nf
    have hexpand : ∫ x in Kn, (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 =
        (∫ x in Kn, u.toFun (x, τ) ^ 2) +
        (∫ x in Kn, u.toFun (x, t₀) ^ 2) -
          2 * ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) := by
      calc
        _ = ∫ x in Kn, (u.toFun (x, τ) ^ 2 + u.toFun (x, t₀) ^ 2 -
            2 * (u.toFun (x, τ) * u.toFun (x, t₀))) := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring_nf
        _ = (∫ x in Kn, u.toFun (x, τ) ^ 2 + u.toFun (x, t₀) ^ 2) -
            ∫ x in Kn, 2 * (u.toFun (x, τ) * u.toFun (x, t₀)) :=
          integral_sub
            (show Integrable (fun x : Vec d => u.toFun (x, τ) ^ 2 +
                u.toFun (x, t₀) ^ 2) (volume.restrict Kn) from hUτsq.add hU₀sq)
            (hprod.const_mul 2)
        _ = _ := by rw [integral_add hUτsq hU₀sq, integral_const_mul]
    have hlocalle :
        (∫ x in euclideanClosedBall (0 : Vec d) R,
          (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) ≤
        ∫ x in Kn, (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := by
      apply setIntegral_mono_set hdiff
      · exact ae_of_all _ fun x => sq_nonneg _
      · exact Eventually.of_forall fun x hx => hK0sub hx
    have hglob : (∫ x in Kn, u.toFun (x, τ) ^ 2) ≤ E τ := by
      have hUτfull :=
        PDE.Parabolic.Cauchy.Energy.cauchy_slice_square_integrable hsT ha f hf u hu hτ
      change (∫ x in Kn, u.toFun (x, τ) ^ 2) ≤ ∫ x : Vec d, u.toFun (x, τ) ^ 2
      apply setIntegral_le_integral hUτfull
      exact ae_of_all _ fun x => sq_nonneg _
    calc
      _ ≤ ∫ x in Kn, (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := hlocalle
      _ = (∫ x in Kn, u.toFun (x, τ) ^ 2) +
          (∫ x in Kn, u.toFun (x, t₀) ^ 2) -
            2 * ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) := hexpand
      _ ≤ E τ + (∫ x in Kn, u.toFun (x, t₀) ^ 2) - 2 * P τ := by
        rw [hpair τ]
        dsimp [B, E, P]
        linarith [hglob]
      _ = B τ := by rfl
  filter_upwards [self_mem_nhdsWithin, hB_event] with τ hτ hτB
  have hle := hcompare τ hτ
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hErr_nonneg τ)] using
    lt_of_le_of_lt hle hτB

private theorem cauchyAbsMoment_continuousOn {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf2 : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) :
    ContinuousOn (fun τ => cauchyAbsMoment δ R hR u τ) (Icc s T) := by
  let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
  have hKcompact : IsCompact K := isCompact_euclideanClosedBall 0 (by positivity)
  have hKfinite : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKcompact.measure_lt_top⟩
  let ξ : Vec d → ℝ := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun
  have hξcont : Continuous ξ :=
    (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.continuous
  have hξmeas : AEStronglyMeasurable ξ (volume.restrict K) := hξcont.aestronglyMeasurable
  have hξbound : ∀ᵐ x ∂(volume.restrict K), ‖ξ x‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).nonneg x
      linarith
    · exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).le_one x
  have hξmem : MemLp ξ 2 (volume.restrict K) := MemLp.of_bound hξmeas 1 hξbound
  obtain ⟨C, hFLip⟩ := cauchyAbsEntropy_lipschitz hδ
  have hFzero : cauchyAbsEntropy δ 0 = 0 := cauchyAbsEntropy_zero δ
  intro t₀ ht₀
  have hlocal := cauchyL1_local_square_tendsto hsT ha f hf2 u hu
    (R := 2 * R) (by positivity) ht₀
  let E : ℝ → ℝ := fun τ => ∫ x in K,
    (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2
  have hE : Tendsto E (𝓝[Icc s T] t₀) (𝓝 0) := by
    simpa only [E, K] using hlocal
  have hsqrt : Tendsto (fun τ => Real.sqrt (E τ)) (𝓝[Icc s T] t₀) (𝓝 0) := by
    have hcomp : Tendsto (Real.sqrt ∘ E) (𝓝[Icc s T] t₀) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hE
    exact hcomp.congr' (Eventually.of_forall fun τ => rfl)
  let Mξ := Real.sqrt (∫ x in K, ξ x ^ 2)
  let L := (C : ℝ) * Mξ
  have hLlim : Tendsto (fun τ => L * Real.sqrt (E τ)) (𝓝[Icc s T] t₀) (𝓝 0) := by
    simpa only [zero_mul, mul_comm] using hsqrt.mul_const L
  have hFmem : ∀ τ ∈ Icc s T,
      MemLp (fun x : Vec d => cauchyAbsEntropy δ (u.toFun (x, τ))) 2
        (volume.restrict K) := by
    intro τ hτ
    have huτ := u.sliceL2loc τ hτ K hKcompact (subset_univ _)
    exact hFLip.comp_memLp hFzero huτ
  have hFint : ∀ τ ∈ Icc s T,
      Integrable (fun x : Vec d => ξ x * cauchyAbsEntropy δ (u.toFun (x, τ)))
        (volume.restrict K) := by
    intro τ hτ
    exact ((hFmem τ hτ).integrable one_le_two).bdd_mul hξmeas (c := 1) hξbound |>.congr
      (Eventually.of_forall fun _ => by simp)
  have hFdiffSq : ∀ τ ∈ Icc s T,
      (∫ x in K, (cauchyAbsEntropy δ (u.toFun (x, τ)) -
        cauchyAbsEntropy δ (u.toFun (x, t₀))) ^ 2) ≤ (C : ℝ) ^ 2 * E τ := by
    intro τ hτ
    have huτ := u.sliceL2loc τ hτ K hKcompact (subset_univ _)
    have hu₀ := u.sliceL2loc t₀ ht₀ K hKcompact (subset_univ _)
    have huDiff := huτ.sub hu₀
    have hFmem' := (hFmem τ hτ).sub (hFmem t₀ ht₀)
    have hIntF := hFmem'.integrable_sq
    have hIntF' : Integrable (fun x : Vec d =>
        (cauchyAbsEntropy δ (u.toFun (x, τ)) -
          cauchyAbsEntropy δ (u.toFun (x, t₀))) ^ 2) (volume.restrict K) := by
      convert hIntF using 1
    have hIntU := huDiff.integrable_sq
    have hIntU' : Integrable (fun x : Vec d =>
        (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) (volume.restrict K) :=
      hIntU.congr (Eventually.of_forall fun _ => rfl)
    calc
      _ ≤ ∫ x in K, (C : ℝ) ^ 2 * (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := by
        apply integral_mono hIntF' (hIntU'.const_mul ((C : ℝ) ^ 2))
        intro x
        have hpoint := hFLip.dist_le_mul (u.toFun (x, τ)) (u.toFun (x, t₀))
        have hpoint' : |cauchyAbsEntropy δ (u.toFun (x, τ)) -
            cauchyAbsEntropy δ (u.toFun (x, t₀))| ≤
            (C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| := by
          simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hpoint
        have hCnonneg : 0 ≤ (C : ℝ) := NNReal.coe_nonneg C
        have hA := abs_nonneg (cauchyAbsEntropy δ (u.toFun (x, τ)) -
          cauchyAbsEntropy δ (u.toFun (x, t₀)))
        have hB : 0 ≤ (C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| :=
          mul_nonneg hCnonneg (abs_nonneg _)
        have hprod : 0 ≤ ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| -
            |cauchyAbsEntropy δ (u.toFun (x, τ)) -
              cauchyAbsEntropy δ (u.toFun (x, t₀))|) *
            ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| +
              |cauchyAbsEntropy δ (u.toFun (x, τ)) -
                cauchyAbsEntropy δ (u.toFun (x, t₀))|) :=
          mul_nonneg (sub_nonneg.mpr hpoint') (add_nonneg hB hA)
        have hsq : |cauchyAbsEntropy δ (u.toFun (x, τ)) -
            cauchyAbsEntropy δ (u.toFun (x, t₀))| ^ 2 ≤
            ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)|) ^ 2 := by
          nlinarith [hprod]
        calc
          _ = |cauchyAbsEntropy δ (u.toFun (x, τ)) -
                cauchyAbsEntropy δ (u.toFun (x, t₀))| ^ 2 := by rw [sq_abs]
          _ ≤ _ := hsq
          _ = _ := by rw [mul_pow, sq_abs]
      _ = (C : ℝ) ^ 2 * E τ := by rw [integral_const_mul]
  have hdiffBound : ∀ τ ∈ Icc s T,
      |(∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, τ))) -
        (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, t₀)))| ≤
          L * Real.sqrt (E τ) := by
    intro τ hτ
    let G : Vec d → ℝ := fun x =>
      cauchyAbsEntropy δ (u.toFun (x, τ)) - cauchyAbsEntropy δ (u.toFun (x, t₀))
    have hGmem : MemLp G 2 (volume.restrict K) := by
      change MemLp ((fun x => cauchyAbsEntropy δ (u.toFun (x, τ))) -
        (fun x => cauchyAbsEntropy δ (u.toFun (x, t₀)))) 2 (volume.restrict K)
      exact (hFmem τ hτ).sub (hFmem t₀ ht₀)
    have hGint := hGmem.integrable one_le_two
    have hprodInt : Integrable (fun x => ξ x * G x) (volume.restrict K) := by
      have hmul := hGint.bdd_mul hξmeas (c := 1) hξbound
      simpa only [mul_comm] using hmul
    have hmomentDiff :
        (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, τ))) -
          ∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, t₀)) =
        ∫ x in K, ξ x * G x := by
      rw [← integral_sub (hFint τ hτ) (hFint t₀ ht₀)]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [G]
      ring
    have hG' : MemL2On K G := hGmem
    have hξ' : MemL2On K ξ := hξmem
    have hupper := PDE.Ch4GreenDecay.integral_mul_le_sqrt hG' hξ'
    have hlower := PDE.Ch4GreenDecay.integral_mul_le_sqrt hG'.neg hξ'
    have hupper' : ∫ x in K, ξ x * G x ≤
        Real.sqrt (∫ x in K, G x ^ 2) * Mξ := by
      simpa only [mul_comm, Mξ] using hupper
    have hlower' : -(∫ x in K, ξ x * G x) ≤
        Real.sqrt (∫ x in K, G x ^ 2) * Mξ := by
      have heq : ∫ x in K, (-G x) * ξ x = -(∫ x in K, ξ x * G x) := by
        rw [show (fun x : Vec d => (-G x) * ξ x) = fun x => -(ξ x * G x) by
          funext x; ring_nf]
        rw [integral_neg]
      calc
        _ = ∫ x in K, (-G x) * ξ x := heq.symm
        _ ≤ Real.sqrt (∫ x in K, (-G x) ^ 2) * Mξ := by
          simpa [Mξ, neg_sq, mul_comm] using hlower
        _ = _ := by
          congr 1
          apply congrArg Real.sqrt
          apply integral_congr_ae
          filter_upwards [] with x
          ring_nf
    have hGabs : |∫ x in K, ξ x * G x| ≤
        Real.sqrt (∫ x in K, G x ^ 2) * Mξ := abs_le.mpr ⟨by linarith [hlower'], hupper'⟩
    have hroot : Real.sqrt (∫ x in K, G x ^ 2) ≤ (C : ℝ) * Real.sqrt (E τ) := by
      have hsqrt := Real.sqrt_le_sqrt (hFdiffSq τ hτ)
      rw [Real.sqrt_mul (sq_nonneg (C : ℝ)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg C)] at hsqrt
      exact hsqrt
    rw [hmomentDiff]
    calc
      _ ≤ Real.sqrt (∫ x in K, G x ^ 2) * Mξ := hGabs
      _ ≤ ((C : ℝ) * Real.sqrt (E τ)) * Mξ :=
        mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
      _ = L * Real.sqrt (E τ) := by dsimp [L]; ring_nf
  have hdist : Tendsto (fun τ => dist
      (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, τ)))
      (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, t₀))))
      (𝓝[Icc s T] t₀) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun τ => dist_nonneg) ?_ hLlim
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [Real.dist_eq]
    exact hdiffBound τ hτ
  have hsub : Tendsto (fun τ =>
      (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, τ))) -
        (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, t₀))))
      (𝓝[Icc s T] t₀) (𝓝 0) := by
    apply (tendsto_iff_dist_tendsto_zero).2
    simpa only [Real.dist_eq, sub_zero] using hdist
  have hcont := hsub.add_const (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, t₀)))
  change Tendsto (fun τ => ∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, τ)))
    (𝓝[Icc s T] t₀) (𝓝 (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, t₀))))
  simpa [sub_add_cancel] using hcont

private theorem cauchyAbsRemainder_cross_bound {d : ℕ} {a : ParCoeffField d}
    {s T : ℝ} (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) (z : Vec d × ℝ) :
    |deriv (cauchyAbsEntropy δ) (u.toFun z) *
        vecDot (matVecMul (a z) (u.grad z))
          (parSpaceGrad (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff
            s T R hR).toFun z)| ≤
      (512 / (δ * R)) * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
  let p := parSpaceGrad (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff
    s T R hR).toFun z
  let G := PDE.Parabolic.Energy.flux a u z
  have hfirst : |deriv (cauchyAbsEntropy δ) (u.toFun z)| ≤
      (16 / δ) * |u.toFun z| := cauchyAbsEntropy_deriv_abs_le_linear hδ _
  have hgrad : vecEuclideanNorm p ≤ 32 / R :=
    PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_spatialGrad_bound
      s T R hR z.1 z.2
  have hGnorm : vecEuclideanNorm G ≤ ∑ i : Fin d, |G i| :=
    vecEuclideanNorm_le_sum_abs G
  have hdot := abs_vecDot_le_vecEuclideanNorm_mul G p
  have hnG : 0 ≤ vecEuclideanNorm G := vecEuclideanNorm_nonneg G
  have hnp : 0 ≤ vecEuclideanNorm p := vecEuclideanNorm_nonneg p
  have hsum : 0 ≤ ∑ i : Fin d, |G i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hcoeff : 0 ≤ (16 : ℝ) / δ := by positivity
  have hscale : 0 ≤ (32 : ℝ) / R := by positivity
  have huabs : 0 ≤ |u.toFun z| := abs_nonneg _
  calc
    |deriv (cauchyAbsEntropy δ) (u.toFun z) * vecDot G p| ≤
        ((16 / δ) * |u.toFun z|) * (vecEuclideanNorm G * vecEuclideanNorm p) := by
      rw [abs_mul]
      exact mul_le_mul hfirst hdot (abs_nonneg _) (mul_nonneg hcoeff huabs)
    _ ≤ ((16 / δ) * |u.toFun z|) * ((∑ i : Fin d, |G i|) * (32 / R)) := by
      gcongr
    _ = (512 / (δ * R)) * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
      simp [G, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant]
      ring

private theorem cauchyAbsRemainder_integrable_Ioc {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) :
    IntegrableOn (cauchyAbsRemainder a u δ R hR)
      ((univ : Set (Vec d)) ×ˢ Ioc s T) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let η : PDE.ParCutoff (univ : Set (Vec d)) (Icc s T) :=
    PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR
  let μ := volume.restrict Q
  have hq : IntegrableOn (PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u) Q := by
    simpa only [Q] using
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_integrable_Ioc ha u
        ⟨hsT.le, le_rfl⟩
  have hmajor : IntegrableOn (PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u) Q := by
    simpa only [Q] using
      PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant_integrable_Ioc ha u
        ⟨hsT.le, le_rfl⟩
  have hsub : Q ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hle : volume.restrict Q ≤
      volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T) := Measure.restrict_mono hsub le_rfl
  have huMeas : AEStronglyMeasurable u.toFun μ :=
    u.memL2.aestronglyMeasurable.mono_measure hle
  have hηMeas : AEStronglyMeasurable η.toFun μ := η.contDiff.continuous.aestronglyMeasurable
  have hηBound : ∀ᵐ z ∂μ, ‖η.toFun z‖ ≤ 1 := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_le]
    rcases PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
      s T R hR z with ⟨h₀, h₁⟩
    exact ⟨by linarith, h₁⟩
  let F'' : ℝ → ℝ := deriv (deriv (cauchyAbsEntropy δ))
  have hF''cont : Continuous F'' := by
    have hF : ContDiff ℝ (⊤ : ℕ∞) (cauchyAbsEntropy δ) := cauchyAbsEntropy_contDiff δ
    have hF2 : ContDiff ℝ (1 + 1 : ℕ∞) (cauchyAbsEntropy δ) :=
      hF.of_le (by norm_num)
    have hF' : ContDiff ℝ 1 (deriv (cauchyAbsEntropy δ)) :=
      (contDiff_succ_iff_deriv.mp hF2).2.2
    exact hF'.continuous_deriv (by norm_num)
  have hF''meas : AEStronglyMeasurable (fun z => F'' (u.toFun z)) μ :=
    hF''cont.comp_aestronglyMeasurable huMeas
  let coeff : Vec d × ℝ → ℝ := fun z => F'' (u.toFun z) * η.toFun z
  have hcoeffMeas : AEStronglyMeasurable coeff μ := hF''meas.mul hηMeas
  have hcoeffBound : ∀ᵐ z ∂μ, ‖coeff z‖ ≤ 16 / δ := by
    filter_upwards [hηBound] with z hη
    rw [Real.norm_eq_abs, abs_mul]
    have hFbound := cauchyAbsEntropy_secondDeriv_abs_le hδ (u.toFun z)
    have hηabs : |η.toFun z| ≤ 1 := by
      rcases PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
        s T R hR z with ⟨hη0, hη1⟩
      exact abs_le.mpr ⟨by linarith, hη1⟩
    have hδpos : 0 ≤ (16 : ℝ) / δ := by positivity
    calc
      |F'' (u.toFun z)| * |η.toFun z| ≤ (16 / δ) * 1 :=
        mul_le_mul hFbound hηabs (abs_nonneg _) hδpos
      _ = 16 / δ := by ring
  have hbulk : Integrable (fun z => coeff z *
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z) μ :=
    hq.bdd_mul hcoeffMeas (c := 16 / δ) hcoeffBound
  let F' : ℝ → ℝ := deriv (cauchyAbsEntropy δ)
  let cross : Vec d × ℝ → ℝ := fun z => F' (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad η.toFun z)
  have hF'cont : Continuous F' :=
    (cauchyAbsEntropy_contDiff δ).continuous_deriv (by norm_num)
  have hF'meas : AEStronglyMeasurable (fun z => F' (u.toFun z)) μ :=
    hF'cont.comp_aestronglyMeasurable huMeas
  have hgradCont : Continuous (parSpaceGrad η.toFun) :=
    PDE.ParabCaccioppoli.continuous_parSpaceGrad η
  have hflux : ∀ i : Fin d, AEStronglyMeasurable
      (fun z => PDE.Parabolic.Energy.flux a u z i) μ := by
    intro i
    exact (PDE.Parabolic.Energy.flux_memLp ha u i).mono_measure hle |>.aestronglyMeasurable
  have hdotMeas : AEStronglyMeasurable
      (fun z => vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad η.toFun z)) μ := by
    have hdot : AEStronglyMeasurable
        (fun z => vecDot (PDE.Parabolic.Energy.flux a u z) (parSpaceGrad η.toFun z)) μ := by
      unfold vecDot
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (hflux i).mul (((continuous_apply i).comp hgradCont).aestronglyMeasurable)
    refine hdot.congr ?_
    filter_upwards [] with z
    simp [PDE.Parabolic.Energy.flux]
  have hcrossMeas : AEStronglyMeasurable cross μ := hF'meas.mul hdotMeas
  have hcross : Integrable cross μ := by
    refine Integrable.mono' (hmajor.const_mul (512 / (δ * R))) hcrossMeas ?_
    filter_upwards [] with z
    dsimp [cross, F', η, Q, μ]
    have hb := cauchyAbsRemainder_cross_bound (a := a) u δ R hδ hR z
    simpa only [PDE.Parabolic.Energy.flux] using hb
  change Integrable (fun z => coeff z *
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z + cross z) μ
  have hsum := hbulk.add hcross
  have heq : (fun z => coeff z * PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z + cross z) =
      cauchyAbsRemainder a u δ R hR := by
    funext z
    simp [coeff, cross, F'', F', η, cauchyAbsRemainder]
  rw [heq]
  exact hsum

theorem cauchySpatialCutoff_zero_outside_closedBall {d : ℕ} (R : ℝ)
    (hR : 0 < R) {x : Vec d}
    (hx : x ∉ euclideanClosedBall 0 (2 * R)) :
    (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x = 0 := by
  have hxball : x ∉ euclideanBall 0 (2 * R) := by
    intro hball
    apply hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    have hn := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hball
    rw [sub_zero] at hn ⊢
    exact le_of_lt hn
  exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).eq_zero_of_not_mem_outer hxball

private theorem cauchyAbsMoment_eq_integral_univ {d : ℕ} {s T : ℝ}
    (δ R : ℝ) (hR : 0 < R)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (τ : ℝ) :
    cauchyAbsMoment δ R hR u τ =
      ∫ x : Vec d,
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
          cauchyAbsEntropy δ (u.toFun (x, τ)) := by
  let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
  have hset :
      (∫ x in (univ : Set (Vec d)),
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
          cauchyAbsEntropy δ (u.toFun (x, τ))) =
      ∫ x in K,
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
          cauchyAbsEntropy δ (u.toFun (x, τ)) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (subset_univ K)]
    intro x hx
    have hxnot : x ∉ euclideanClosedBall 0 (2 * R) := by simpa [K] using hx.2
    rw [cauchySpatialCutoff_zero_outside_closedBall R hR hxnot]
    simp
  calc
    _ = ∫ x in K,
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
          cauchyAbsEntropy δ (u.toFun (x, τ)) := rfl
    _ = ∫ x in (univ : Set (Vec d)),
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
          cauchyAbsEntropy δ (u.toFun (x, τ)) := hset.symm
    _ = ∫ x : Vec d,
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun x *
          cauchyAbsEntropy δ (u.toFun (x, τ)) := by rw [setIntegral_univ]

private noncomputable def cauchyAbsRemainderSlice {d : ℕ} {s T : ℝ}
    (a : ParCoeffField d) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (δ R : ℝ) (hR : 0 < R) (τ : ℝ) : ℝ :=
  ∫ x : Vec d, cauchyAbsRemainder a u δ R hR (x, τ)

private theorem cauchyAbsRenormalization_test_identity {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) {t : ℝ}
    (ht : t ∈ Icc s T) (hst : s < t) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθsupport : tsupport θ ⊆ Ioo s t) :
    ∫ τ in Ioo s t, cauchyAbsMoment δ R hR u τ * deriv θ τ =
      ∫ τ in Ioo s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ := by
  let F : ℝ → ℝ := cauchyAbsEntropy δ
  let ξ : Vec d → ℝ := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun
  let η : PDE.ParCutoff (univ : Set (Vec d)) (Icc s T) :=
    PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR
  have htimeSupport : tsupport θ ⊆ interior (Icc s T) :=
    hθsupport.trans (interior_maximal
      (fun τ hτ => ⟨hτ.1.le, hτ.2.le.trans ht.2⟩) isOpen_Ioo)
  let φ : PDE.ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)) :=
    { toFun := fun z => θ z.2 * ξ z.1
      contDiff := PDE.Parabolic.WeakSlice.contDiff_prod hθ
        ((PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.of_le (by norm_num))
      hasCompactSupport := PDE.Parabolic.WeakSlice.hasCompactSupport_prod hθc
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).hasCompactSupport
      tsupport_subset := by
        exact PDE.Parabolic.WeakSlice.tsupport_prod_subset.trans
          (Set.prod_mono (subset_univ _) htimeSupport) }
  have hφsupport : tsupport φ.toFun ⊆ (univ : Set (Vec d)) ×ˢ Ioo s t :=
    PDE.Parabolic.WeakSlice.tsupport_prod_subset.trans
      (Set.prod_mono (subset_univ _) hθsupport)
  have hFcont : ContDiff ℝ 2 F := by
    simpa [F] using (cauchyAbsEntropy_contDiff δ).of_le (by norm_num)
  have hFLip : ∃ C : NNReal, LipschitzWith C F := by
    simpa [F] using cauchyAbsEntropy_lipschitz hδ
  have hF'bound : ∃ C' : NNReal, ∀ y : ℝ, |deriv F y| ≤ C' := by
    refine ⟨1, ?_⟩
    intro y
    simpa [F] using cauchyAbsEntropy_deriv_abs_le_one hδ y
  have hF''bound : ∃ C' : NNReal, ∀ y : ℝ, |deriv (deriv F) y| ≤ C' := by
    refine ⟨⟨16 / δ, by positivity⟩, ?_⟩
    intro y
    change |deriv (deriv (cauchyAbsEntropy δ)) y| ≤
      ((⟨16 / δ, by positivity⟩ : NNReal) : ℝ)
    exact cauchyAbsEntropy_secondDeriv_abs_le hδ y
  obtain ⟨hRenInt, hRenZero⟩ :=
    PDE.Parabolic.Chain.weak_solution_renormalization_H1
      isOpen_univ Set.ordConnected_Icc ha u hu F hFcont hFLip hF'bound hF''bound φ
      ⟨le_rfl, hsT.le⟩ ht hst hφsupport
  have hηval (z : Vec d × ℝ) : η.toFun z = ξ z.1 := by
    change (1 : ℝ) * ξ z.1 = ξ z.1
    simp
  have hgradEq (z : Vec d × ℝ) :
      spaceGradC1 ξ z.1 = parSpaceGrad η.toFun z := by
    change spaceGradC1 (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun z.1 =
      parSpaceGrad (fun w : Vec d × ℝ => (1 : ℝ) *
        (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun w.1) z
    rw [PDE.Parabolic.WeakSlice.parSpaceGrad_prod
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
      ((PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.of_le (by norm_num))]
    simp
  have hformula (z : Vec d × ℝ) :
      PDE.Parabolic.Chain.renormalizedIntegrand a u F φ.toFun z =
        -(F (u.toFun z) * deriv θ z.2 * ξ z.1) +
          θ z.2 * cauchyAbsRemainder a u δ R hR z := by
    unfold PDE.Parabolic.Chain.renormalizedIntegrand
    rw [PDE.Parabolic.WeakSlice.parTimeDeriv_prod hθ
      ((PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.of_le (by norm_num)),
      PDE.Parabolic.WeakSlice.parSpaceGrad_prod hθ
        ((PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.of_le (by norm_num)),
      hgradEq z]
    dsimp [F, cauchyAbsRemainder, ξ, η,
      PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff,
      PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity, φ]
    simp only [one_mul]
    rw [PDE.Parabolic.WeakSlice.vecDot_smul_right']
    rw [vecDot_comm (u.grad z) (matVecMul (a z) (u.grad z))]
    ring
  have hremT := cauchyAbsRemainder_integrable_Ioc hsT ha u δ R hδ hR
  have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆
      (univ : Set (Vec d)) ×ˢ Ioc s T :=
    prod_mono subset_rfl (Ioc_subset_Ioc_right ht.2)
  have hrem : IntegrableOn (cauchyAbsRemainder a u δ R hR)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := hremT.mono_set hQsub
  obtain ⟨Mθ, hMθ⟩ := hθ.continuous.bounded_above_of_compact_support hθc
  have hθmeas : AEStronglyMeasurable (fun z : Vec d × ℝ => θ z.2)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)) :=
    (hθ.continuous.comp continuous_snd).aestronglyMeasurable
  have hθbound : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      ‖θ z.2‖ ≤ Mθ := Filter.Eventually.of_forall fun z => hMθ z.2
  have hθrem : IntegrableOn
      (fun z => θ z.2 * cauchyAbsRemainder a u δ R hR z)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := hrem.bdd_mul hθmeas (c := Mθ) hθbound
  have hfirst : IntegrableOn
      (fun z => -(F (u.toFun z) * deriv θ z.2 * ξ z.1))
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
    have hsub := hRenInt.sub hθrem
    refine hsub.congr ?_
    filter_upwards [] with z
    change PDE.Parabolic.Chain.renormalizedIntegrand a u F φ.toFun z -
      θ z.2 * cauchyAbsRemainder a u δ R hR z = _
    rw [hformula z]
    ring
  have hsum :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        PDE.Parabolic.Chain.renormalizedIntegrand a u F φ.toFun z) =
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        -(F (u.toFun z) * deriv θ z.2 * ξ z.1)) +
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        θ z.2 * cauchyAbsRemainder a u δ R hR z := by
    rw [← integral_add hfirst hθrem]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    exact hformula z
  have hfirstFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hfirst
  have hremFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hθrem
  have hinnerFirst (τ : ℝ) :
      ∫ x in (univ : Set (Vec d)),
        -(F (u.toFun (x, τ)) * deriv θ τ * ξ x) =
      -(cauchyAbsMoment δ R hR u τ * deriv θ τ) := by
    calc
      _ = ∫ x in (univ : Set (Vec d)),
          (-deriv θ τ) * (ξ x * F (u.toFun (x, τ))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        ring_nf
      _ = (-deriv θ τ) * ∫ x in (univ : Set (Vec d)),
          ξ x * F (u.toFun (x, τ)) := by rw [MeasureTheory.integral_const_mul]
      _ = -(cauchyAbsMoment δ R hR u τ * deriv θ τ) := by
        rw [setIntegral_univ, cauchyAbsMoment_eq_integral_univ δ R hR u τ]
        simp only [F, ξ]
        ring
  have hinnerRem (τ : ℝ) :
      ∫ x in (univ : Set (Vec d)),
        θ τ * cauchyAbsRemainder a u δ R hR (x, τ) =
      θ τ * cauchyAbsRemainderSlice a u δ R hR τ := by
    rw [MeasureTheory.integral_const_mul]
    simp only [setIntegral_univ, cauchyAbsRemainderSlice]
  have hfirstTime :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        -(F (u.toFun z) * deriv θ z.2 * ξ z.1)) =
      -∫ τ in Ioc s t, cauchyAbsMoment δ R hR u τ * deriv θ τ := by
    rw [hfirstFubini.2]
    calc
      _ = ∫ τ in Ioc s t,
          -(cauchyAbsMoment δ R hR u τ * deriv θ τ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        exact hinnerFirst τ
      _ = -∫ τ in Ioc s t, cauchyAbsMoment δ R hR u τ * deriv θ τ := by
        rw [MeasureTheory.integral_neg]
  have hremTime :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        θ z.2 * cauchyAbsRemainder a u δ R hR z) =
      ∫ τ in Ioc s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ := by
    rw [hremFubini.2]
    calc
      _ = ∫ τ in Ioc s t,
          θ τ * cauchyAbsRemainderSlice a u δ R hR τ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        exact hinnerRem τ
      _ = ∫ τ in Ioc s t,
          cauchyAbsRemainderSlice a u δ R hR τ * θ τ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        ring
  have hzθ : ∀ τ, τ ∉ Ioo s t → θ τ = 0 := by
    intro τ hτ
    exact image_eq_zero_of_notMem_tsupport (fun hmem => hτ (hθsupport hmem))
  have hzθ' : ∀ τ, τ ∉ Ioo s t → deriv θ τ = 0 := by
    intro τ hτ
    exact image_eq_zero_of_notMem_tsupport
      (fun hmem => hτ (hθsupport (tsupport_deriv_subset hmem)))
  have hIocEq :
      ∫ τ in Ioc s t, cauchyAbsMoment δ R hR u τ * deriv θ τ =
      ∫ τ in Ioc s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ := by
    have hsum0 :
        (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          -(F (u.toFun z) * deriv θ z.2 * ξ z.1)) +
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          θ z.2 * cauchyAbsRemainder a u δ R hR z = 0 := by
      rw [← hsum, hRenZero]
    rw [hfirstTime, hremTime] at hsum0
    linarith
  have hleft :
      (∫ τ in Ioc s t, cauchyAbsMoment δ R hR u τ * deriv θ τ) =
      ∫ τ in Ioo s t, cauchyAbsMoment δ R hR u τ * deriv θ τ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      Ioo_subset_Ioc_self (fun τ hτ => by rw [hzθ' τ hτ.2, mul_zero])
  have hright :
      (∫ τ in Ioc s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ) =
      ∫ τ in Ioo s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      Ioo_subset_Ioc_self (fun τ hτ => by rw [hzθ τ hτ.2, mul_zero])
  calc
    _ = ∫ τ in Ioc s t, cauchyAbsMoment δ R hR u τ * deriv θ τ := hleft.symm
    _ = ∫ τ in Ioc s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ := hIocEq
    _ = ∫ τ in Ioo s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ := hright

private theorem cauchyAbsMoment_endpoint_identity {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    cauchyAbsMoment δ R hR u s - cauchyAbsMoment δ R hR u t =
      ∫ τ in Ioo s t, cauchyAbsRemainderSlice a u δ R hR τ := by
  let m₀ : ℝ → ℝ := fun τ => cauchyAbsMoment δ R hR u τ
  have hm₀ : ContinuousOn m₀ (Icc s T) :=
    cauchyAbsMoment_continuousOn hsT ha f hf u hu δ R hδ hR
  let clip : ℝ → ℝ := fun τ => max s (min T τ)
  have hclipCont : Continuous clip := by fun_prop
  have hclipRange (τ : ℝ) : clip τ ∈ Icc s T := by
    dsimp [clip]
    exact ⟨le_max_left _ _, max_le hsT.le (min_le_left _ _)⟩
  let m : ℝ → ℝ := fun τ => m₀ (clip τ)
  have hm : Continuous m := by
    have hmc : ContinuousOn m univ := by
      dsimp [m]
      exact hm₀.comp hclipCont.continuousOn (fun τ _ => hclipRange τ)
    exact continuousOn_univ.mp hmc
  have hclipEq (τ : ℝ) (hτ : τ ∈ Icc s T) : clip τ = τ := by
    dsimp [clip]
    rw [min_eq_right hτ.2, max_eq_right hτ.1]
  have hremST := cauchyAbsRemainder_integrable_Ioc hsT ha u δ R hδ hR
  have hremFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hremST
  let g : ℝ → ℝ := fun τ => cauchyAbsRemainderSlice a u δ R hR τ
  have hgST : IntegrableOn g (Ioc s T) := by
    simpa only [g, cauchyAbsRemainderSlice, setIntegral_univ] using hremFubini.1
  have hgIoc : IntegrableOn g (Ioc s t) := hgST.mono_set
    (Ioc_subset_Ioc_right ht.2)
  have hg : IntegrableOn g (Ioo s t) := hgIoc.mono_set Ioo_subset_Ioc_self
  have hid := PDE.Parabolic.WeakSlice.dubois_reymond hst m g hm hg
    (fun θ hθ hθc hθsupport => by
      calc
        _ = ∫ τ in Ioo s t, cauchyAbsMoment δ R hR u τ * deriv θ τ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro τ hτ
          simp only [m, m₀]
          rw [hclipEq τ ⟨hτ.1.le, hτ.2.le.trans ht.2⟩]
        _ = ∫ τ in Ioo s t, cauchyAbsRemainderSlice a u δ R hR τ * θ τ :=
          cauchyAbsRenormalization_test_identity hsT ha u hu.1 δ R hδ hR ht hst
            hθ hθc hθsupport
        _ = ∫ τ in Ioo s t, g τ * θ τ := by simp only [g])
  have hms : m s = cauchyAbsMoment δ R hR u s := by
    dsimp [m, m₀]
    rw [hclipEq s ⟨le_rfl, hsT.le⟩]
  have hmt : m t = cauchyAbsMoment δ R hR u t := by
    dsimp [m, m₀]
    rw [hclipEq t ht]
  rw [hms, hmt] at hid
  simpa only [g] using hid

private theorem cauchyAbsMoment_initial_bound {d : ℕ} {a : ParCoeffField d}
    {s T : ℝ} (hsT : s < T) (f : Vec d → ℝ) (hf1 : Integrable f volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (δ R : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) :
    cauchyAbsMoment δ R hR u s ≤ ∫ x : Vec d, |f x| := by
  let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
  have hKcompact : IsCompact K := isCompact_euclideanClosedBall 0 (by positivity)
  have hKfinite : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKcompact.measure_lt_top⟩
  let ξ : Vec d → ℝ := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).toFun
  have hξnonneg : ∀ x, 0 ≤ ξ x := by
    intro x
    exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).nonneg x
  have hξle : ∀ x, ξ x ≤ 1 := by
    intro x
    exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).le_one x
  have hslice := u.sliceL2loc s ⟨le_rfl, hsT.le⟩ K hKcompact (subset_univ _)
  obtain ⟨C, hLip⟩ := cauchyAbsEntropy_lipschitz hδ
  have hFzero : cauchyAbsEntropy δ 0 = 0 := cauchyAbsEntropy_zero δ
  have hFmem : MemLp (fun x : Vec d => cauchyAbsEntropy δ (u.toFun (x, s)))
      2 (volume.restrict K) := hLip.comp_memLp hFzero hslice
  have hFint : Integrable (fun x : Vec d => ξ x *
      cauchyAbsEntropy δ (u.toFun (x, s))) (volume.restrict K) := by
    have hξmeas : AEStronglyMeasurable ξ (volume.restrict K) :=
      (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff R hR).smooth.continuous.aestronglyMeasurable
    have hξbound : ∀ᵐ x ∂(volume.restrict K), ‖ξ x‖ ≤ 1 := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hξnonneg x], hξle x⟩
    exact (hFmem.integrable one_le_two).bdd_mul hξmeas (c := 1) hξbound |>.congr
      (Eventually.of_forall fun _ => by simp)
  have hAbsInt : Integrable (fun x : Vec d => |f x|) (volume.restrict K) :=
    hf1.norm.mono_measure (Measure.restrict_le_self)
  have hinit : ∀ᵐ x : Vec d, u.toFun (x, s) = f x := hu.2
  have hinitK : ∀ᵐ x ∂(volume.restrict K), u.toFun (x, s) = f x := by
    apply (ae_restrict_iff' (measurableSet_euclideanClosedBall 0 (2 * R))).2
    filter_upwards [hinit] with x hx
    intro _
    exact hx
  have hpoint : ∀ᵐ x ∂(volume.restrict K),
      ξ x * cauchyAbsEntropy δ (u.toFun (x, s)) ≤ |f x| := by
    filter_upwards [hinitK] with x hx
    rw [hx]
    have hF0 := cauchyAbsEntropy_nonneg hδ (f x)
    have hF1 := cauchyAbsEntropy_le_abs hδ (f x)
    exact (mul_le_mul_of_nonneg_left hF1 (hξnonneg x)).trans
      (by nlinarith [hξle x, hF0])
  have hloc :
      (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, s))) ≤
        ∫ x in K, |f x| := integral_mono_ae hFint hAbsInt hpoint
  have hglob : (∫ x in K, |f x|) ≤ ∫ x : Vec d, |f x| := by
    apply setIntegral_le_integral hf1.norm
    exact ae_of_all _ fun _ => abs_nonneg _
  change (∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, s))) ≤ _ at hloc
  rw [show cauchyAbsMoment δ R hR u s =
    ∫ x in K, ξ x * cauchyAbsEntropy δ (u.toFun (x, s)) by rfl]
  exact hloc.trans hglob

private theorem cauchyAbsRemainder_integral_lower_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) {t : ℝ}
    (ht : t ∈ Icc s T) :
    -((512 / (δ * R)) *
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
          PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) ≤
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        cauchyAbsRemainder a u δ R hR z := by
  let Qmax : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let Qt : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let C : ℝ := 512 / (δ * R)
  have hQsub : Qt ⊆ Qmax := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1, hz.2.2.trans ht.2⟩⟩
  have hQslab : Qt ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hmajorMax : IntegrableOn (PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u) Qmax := by
    simpa only [Qmax] using
      PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant_integrable_Ioc ha u ⟨hsT.le, le_rfl⟩
  have hmajorT : IntegrableOn (PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u) Qt :=
    hmajorMax.mono_set hQsub
  have hmajorNonneg : ∀ᵐ z ∂(volume.restrict Qmax),
      0 ≤ PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
    filter_upwards [] with z
    apply mul_nonneg (abs_nonneg _)
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hmajorSetLe :
      ∫ z in Qt, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z ≤
        ∫ z in Qmax, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z :=
    setIntegral_mono_set hmajorMax hmajorNonneg (ae_of_all _ fun z hz => hQsub hz)
  have hremMax := cauchyAbsRemainder_integrable_Ioc hsT ha u δ R hδ hR
  have hremT : IntegrableOn (cauchyAbsRemainder a u δ R hR) Qt :=
    hremMax.mono_set hQsub
  have henergyNonneg : ∀ᵐ z ∂(volume.restrict Qt),
      0 ≤ PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z :=
    (PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity_nonneg_ae ha u).filter_mono
      (ae_mono (Measure.restrict_mono hQslab le_rfl))
  have hpoint : (fun z : Vec d × ℝ => -(C *
      PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z)) ≤ᵐ[
        volume.restrict Qt] (cauchyAbsRemainder a u δ R hR) := by
    filter_upwards [henergyNonneg] with z hq
    have hF'' := cauchyAbsEntropy_secondDeriv_nonneg hδ (u.toFun z)
    rcases PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff_nonneg_le_one
      s T R hR z with ⟨hcut, _⟩
    have hbulk : 0 ≤ deriv (deriv (cauchyAbsEntropy δ)) (u.toFun z) *
        (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff s T R hR).toFun z *
          PDE.Parabolic.Cauchy.Energy.cauchyEnergyDensity a u z :=
      mul_nonneg (mul_nonneg hF'' hcut) hq
    have hcross := cauchyAbsRemainder_cross_bound (a := a) u δ R hδ hR z
    have hcrossLower : -(C * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) ≤
        deriv (cauchyAbsEntropy δ) (u.toFun z) *
          vecDot (matVecMul (a z) (u.grad z))
            (parSpaceGrad (PDE.Parabolic.Cauchy.Energy.cauchyParabolicCutoff
              s T R hR).toFun z) := by
      have := (abs_le.mp hcross).1
      simpa only [C] using this
    dsimp [cauchyAbsRemainder]
    simpa only [zero_add, C] using add_le_add hbulk hcrossLower
  have hremLower :
      ∫ z in Qt, -(C * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) ≤
        ∫ z in Qt, cauchyAbsRemainder a u δ R hR z := by
    have hleftInt : IntegrableOn (fun z : Vec d × ℝ =>
        -(C * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z)) Qt := by
      have h := hmajorT.const_mul (-C)
      refine h.congr ?_
      filter_upwards [] with z
      ring
    exact integral_mono_ae hleftInt hremT hpoint
  have hleftEq : (∫ z in Qt, -(C *
      PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z)) =
      -(C * ∫ z in Qt, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) := by
    rw [show (fun z : Vec d × ℝ => -(C *
        PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z)) =
      fun z => (-C) * PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z by
        funext z; ring, MeasureTheory.integral_const_mul]
    ring
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htail : -(C * ∫ z in Qmax,
      PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) ≤
      ∫ z in Qt, cauchyAbsRemainder a u δ R hR z := by
    have htail' := hremLower
    rw [hleftEq] at htail'
    calc
      -(C * ∫ z in Qmax, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) ≤
          -(C * ∫ z in Qt, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z) := by
        have hmul := mul_le_mul_of_nonneg_left hmajorSetLe hC
        linarith
      _ ≤ ∫ z in Qt, cauchyAbsRemainder a u δ R hR z := htail'
  simpa only [C, Qmax, Qt] using htail

theorem cauchyAbsMoment_upper_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (hf1 : Integrable f volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Icc s T) :
    cauchyAbsMoment δ R hR u t ≤
      (∫ x : Vec d, |f x|) + (512 / (δ * R)) *
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
          PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
  by_cases hst : s < t
  · let Qt : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
    let Qmax : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
    have hremST := cauchyAbsRemainder_integrable_Ioc hsT ha u δ R hδ hR
    have hremT : IntegrableOn (cauchyAbsRemainder a u δ R hR) Qt :=
      hremST.mono_set (prod_mono subset_rfl (Ioc_subset_Ioc_right ht.2))
    have hFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hremT
    let g : ℝ → ℝ := fun τ => cauchyAbsRemainderSlice a u δ R hR τ
    have hFub :
        ∫ z in Qt, cauchyAbsRemainder a u δ R hR z = ∫ τ in Ioc s t, g τ := by
      simpa only [Qt, g, cauchyAbsRemainderSlice, setIntegral_univ] using hFubini.2
    have htimeEq : (∫ τ in Ioo s t, g τ) = ∫ τ in Ioc s t, g τ := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    have hendpoint := cauchyAbsMoment_endpoint_identity hsT ha f hf u hu
      δ R hδ hR ht hst
    have hinitial := cauchyAbsMoment_initial_bound hsT f hf1 u hu δ R hδ hR
    have hremLower := cauchyAbsRemainder_integral_lower_bound hsT ha u δ R hδ hR ht
    have hdiff : cauchyAbsMoment δ R hR u s - cauchyAbsMoment δ R hR u t =
        ∫ z in Qt, cauchyAbsRemainder a u δ R hR z := by
      calc
        _ = ∫ τ in Ioo s t, g τ := by simpa only [g] using hendpoint
        _ = ∫ τ in Ioc s t, g τ := htimeEq
        _ = ∫ z in Qt, cauchyAbsRemainder a u δ R hR z := hFub.symm
    have hfluxNonneg : 0 ≤ ∫ z in Qmax,
        PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
      apply setIntegral_nonneg_of_ae_restrict
      filter_upwards [] with z
      apply mul_nonneg (abs_nonneg _)
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    have hfluxNonneg' : 0 ≤ (512 / (δ * R)) *
        ∫ z in Qmax, PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z :=
      mul_nonneg (by positivity) hfluxNonneg
    linarith [hdiff, hremLower, hinitial]
  · have hst' : t = s := le_antisymm (not_lt.mp hst) ht.1
    rw [hst']
    have hinitial := cauchyAbsMoment_initial_bound hsT f hf1 u hu δ R hδ hR
    have hfluxNonneg : 0 ≤ ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        PDE.Parabolic.Cauchy.Energy.cauchyFluxMajorant a u z := by
      apply setIntegral_nonneg_of_ae_restrict
      filter_upwards [] with z
      apply mul_nonneg (abs_nonneg _)
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [mul_nonneg (by positivity : 0 ≤ 512 / (δ * R)) hfluxNonneg]

theorem cauchyL1_slice_aestronglyMeasurable {d : ℕ} {s T t : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (ht : t ∈ Icc s T) :
    AEStronglyMeasurable (parSlice u.toFun t) volume := by
  let K : ℕ → Set (Vec d) := fun n => euclideanClosedBall 0 ((n : ℝ) + 1)
  have hKcompact (n : ℕ) : IsCompact (K n) :=
    isCompact_euclideanClosedBall 0 (by positivity)
  have hKmeas (n : ℕ) : MeasurableSet (K n) :=
    measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
  have hHmem (n : ℕ) : MemLp ((K n).indicator (parSlice u.toFun t)) 2 volume := by
    rw [memLp_indicator_iff_restrict (hKmeas n)]
    exact u.sliceL2loc t ht (K n) (hKcompact n) (subset_univ _)
  have hHmeas (n : ℕ) :
      AEStronglyMeasurable ((K n).indicator (parSlice u.toFun t)) volume :=
    (hHmem n).aestronglyMeasurable
  have hlimit : ∀ x : Vec d,
      Tendsto (fun n : ℕ => (K n).indicator (parSlice u.toFun t) x) atTop
        (𝓝 (parSlice u.toFun t x)) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
    have hEventually : ∀ᶠ n : ℕ in atTop,
        x ∈ euclideanClosedBall 0 ((n : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hnorm : vecEuclideanNorm (x - (0 : Vec d)) ≤ (n : ℝ) + 1 := by
        rw [sub_zero]
        linarith
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 hnorm
    have heq : ∀ᶠ n : ℕ in atTop,
        (K n).indicator (parSlice u.toFun t) x = parSlice u.toFun t x := by
      filter_upwards [hEventually] with n hn
      simp [K, hn]
    exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)
  exact aestronglyMeasurable_of_tendsto_ae atTop hHmeas
    (ae_of_all _ hlimit)

end PDE.Parabolic.Cauchy.L1
