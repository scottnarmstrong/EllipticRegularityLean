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
public import EllipticRegularity.Parabolic.Cauchy.Energy.PositivityNegativeEnergy

/-! # Negative-energy moments for Cauchy positivity -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set Filter Topology intervalIntegral

theorem cauchy_energy_bulk_integral_continuous {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) :
    ContinuousOn (fun τ => ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s τ,
      cauchyEnergyDensity a u z) (Icc s T) := by
  have hq : IntegrableOn (cauchyEnergyDensity a u)
      ((univ : Set (Vec d)) ×ˢ Icc s T) := cauchyEnergyDensity_integrable ha u
  let qbar : ℝ → ℝ := fun τ => ∫ x : Vec d, cauchyEnergyDensity a u (x, τ)
  have hqbar := PDE.Parabolic.WeakSlice.integral_prod_slices hq
  have hqbar_int : IntegrableOn qbar (Icc s T) := by
    simpa only [qbar, setIntegral_univ] using hqbar.1
  have hprim : ContinuousOn (fun τ => ∫ r in Ioc s τ, qbar r)
      (Icc s T) := by
    exact continuousOn_primitive hqbar_int
  refine hprim.congr ?_
  intro τ hτ
  have hsub : (univ : Set (Vec d)) ×ˢ Ioc s τ ⊆
      (univ : Set (Vec d)) ×ˢ Icc s T :=
    prod_mono subset_rfl fun r hr => ⟨hr.1.le, hr.2.trans hτ.2⟩
  have hqτ := PDE.Parabolic.WeakSlice.integral_prod_slices
    ((hq.mono_set hsub))
  simpa only [qbar, setIntegral_univ] using hqτ.2

theorem cauchy_slice_square_integral_continuous {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) :
    ContinuousOn (fun τ => ∫ x : Vec d, u.toFun (x, τ) ^ 2) (Icc s T) := by
  have hbulk := cauchy_energy_bulk_integral_continuous ha u
  have hcont' : ContinuousOn (fun τ => (∫ x : Vec d, f x ^ 2) -
      2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s τ, cauchyEnergyDensity a u z)
      (Icc s T) := by
    have hbulk2 : ContinuousOn (fun τ => 2 * ∫ z in
        (univ : Set (Vec d)) ×ˢ Ioc s τ, cauchyEnergyDensity a u z) (Icc s T) := by
      exact hbulk.const_mul 2
    exact continuousOn_const.sub hbulk2
  refine hcont'.congr ?_
  intro τ hτ
  have hId := cauchy_energy_identity_real hsT ha f hf u hu hτ
  linarith

theorem cauchy_slice_local_square_tendsto {d : ℕ} {lam Lam : ℝ}
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
        exact le_trans (le_of_lt hN) (by linarith)
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 hnorm
    · intro n
      exact measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
  have hu₀sq : Integrable (fun x : Vec d => u.toFun (x, t₀) ^ 2) volume :=
    cauchy_slice_square_integrable hsT ha f hf u hu ht₀
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
    simpa only [E] using cauchy_slice_square_integral_continuous hsT ha f hf u hu
  have hPcont : ContinuousOn P (Icc s T) := by
    simpa only [P, setIntegral_univ] using hpairCont
  have hpair (τ : ℝ) : P τ =
      ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) := by
    calc
      P τ = ∫ x : Vec d,
          Kn.indicator (fun x => u.toFun (x, τ) * u.toFun (x, t₀)) x := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Kn <;> simp [ψ, hx]
      _ = ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) :=
        integral_indicator hKmeas
  have hBcont : ContinuousOn B (Icc s T) := by
    change ContinuousOn ((fun τ => E τ +
      (∫ x in Kn, u.toFun (x, t₀) ^ 2)) - (fun τ => 2 * P τ)) (Icc s T)
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
      change Integrable (parSlice u.toFun τ * parSlice u.toFun t₀)
        (volume.restrict Kn)
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
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          ring_nf
        _ = (∫ x in Kn, u.toFun (x, τ) ^ 2 + u.toFun (x, t₀) ^ 2) -
            ∫ x in Kn, 2 * (u.toFun (x, τ) * u.toFun (x, t₀)) := by
          exact integral_sub (hUτsq.add hU₀sq) (hprod.const_mul 2)
        _ = _ := by
          rw [integral_add hUτsq hU₀sq, MeasureTheory.integral_const_mul]
    have hlocalle :
        (∫ x in euclideanClosedBall (0 : Vec d) R,
          (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) ≤
        ∫ x in Kn, (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := by
      apply setIntegral_mono_set hdiff
      · exact ae_of_all _ fun x => sq_nonneg _
      · exact Filter.Eventually.of_forall fun x hx => hK0sub hx
    have hglob : (∫ x in Kn, u.toFun (x, τ) ^ 2) ≤ E τ := by
      have hUτfull := cauchy_slice_square_integrable hsT ha f hf u hu hτ
      change (∫ x in Kn, u.toFun (x, τ) ^ 2) ≤ ∫ x : Vec d, u.toFun (x, τ) ^ 2
      apply setIntegral_le_integral hUτfull
      exact ae_of_all _ fun x => sq_nonneg _
    calc
      (∫ x in euclideanClosedBall (0 : Vec d) R,
        (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) ≤
          ∫ x in Kn, (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := hlocalle
      _ = (∫ x in Kn, u.toFun (x, τ) ^ 2) +
          (∫ x in Kn, u.toFun (x, t₀) ^ 2) -
            2 * ∫ x in Kn, u.toFun (x, τ) * u.toFun (x, t₀) := hexpand
      _ ≤ E τ + (∫ x in Kn, u.toFun (x, t₀) ^ 2) - 2 * P τ := by
        rw [hpair τ]
        dsimp [B, E, P]
        linarith [hglob]
  filter_upwards [self_mem_nhdsWithin, hB_event] with τ hτ hτB
  have hle := hcompare τ hτ
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hErr_nonneg τ)] using
    lt_of_le_of_lt hle hτB

noncomputable def cauchyNegativeMoment {d : ℕ} {s T : ℝ} (ε R : ℝ)
    (hR : 0 < R) (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (τ : ℝ) : ℝ :=
  ∫ x in euclideanClosedBall 0 (2 * R),
    (cauchySpatialCutoff R hR).toFun x * cauchyNegativeEnergy ε (u.toFun (x, τ))

theorem cauchyNegativeMoment_continuousOn {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    ContinuousOn (fun τ => ∫ x in euclideanClosedBall 0 (2 * R),
      (cauchySpatialCutoff R hR).toFun x * cauchyNegativeEnergy ε (u.toFun (x, τ)))
      (Icc s T) := by
  let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
  have hKcompact : IsCompact K := isCompact_euclideanClosedBall 0 (by positivity)
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hKcompact.measure_lt_top⟩
  let ξ : Vec d → ℝ := (cauchySpatialCutoff R hR).toFun
  let F : ℝ → ℝ := cauchyNegativeEnergy ε
  have hFzero : F 0 = 0 := cauchyNegativeEnergy_zero_of_nonneg ε hε le_rfl
  obtain ⟨C, hFLip⟩ := cauchyNegativeEnergy_lipschitz ε hε
  have hξcont : Continuous ξ := by
    dsimp [ξ]
    exact (cauchySpatialCutoff R hR).smooth.continuous
  have hξmeas : AEStronglyMeasurable ξ (volume.restrict K) := hξcont.aestronglyMeasurable
  have hξbound : ∀ᵐ x ∂(volume.restrict K), ‖ξ x‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h := (cauchySpatialCutoff R hR).nonneg x
      linarith
    · exact (cauchySpatialCutoff R hR).le_one x
  have hξmem : MemLp ξ 2 (volume.restrict K) := by
    exact MemLp.of_bound hξmeas 1 hξbound
  intro t₀ ht₀
  have hlocal := cauchy_slice_local_square_tendsto hsT ha f hf u hu
    (R := 2 * R) (by positivity) ht₀
  let E : ℝ → ℝ := fun τ => ∫ x in K,
    (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2
  have hE : Tendsto E (𝓝[Icc s T] t₀) (𝓝 0) := by
    simpa only [E, K] using hlocal
  have hsqrt : Tendsto (fun τ => Real.sqrt (E τ)) (𝓝[Icc s T] t₀) (𝓝 0) := by
    have hcomp : Tendsto (Real.sqrt ∘ E) (𝓝[Icc s T] t₀) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hE
    have heq : (fun τ => Real.sqrt (E τ)) = Real.sqrt ∘ E := by
      funext τ
      rfl
    rw [heq]
    exact hcomp
  let Mξ := Real.sqrt (∫ x in K, ξ x ^ 2)
  let L := (C : ℝ) * Mξ
  have hLnonneg : 0 ≤ L := mul_nonneg (NNReal.coe_nonneg _) (Real.sqrt_nonneg _)
  have hLlim : Tendsto (fun τ => L * Real.sqrt (E τ)) (𝓝[Icc s T] t₀) (𝓝 0) := by
    simpa only [zero_mul, mul_comm] using hsqrt.mul_const L
  have hFτmem : ∀ τ ∈ Icc s T,
      MemLp (F ∘ parSlice u.toFun τ) 2 (volume.restrict K) := by
    intro τ hτ
    have huτ := u.sliceL2loc τ hτ K hKcompact (subset_univ _)
    exact hFLip.comp_memLp hFzero huτ
  have hFτint : ∀ τ ∈ Icc s T,
      Integrable (fun x : Vec d => ξ x * F (u.toFun (x, τ))) (volume.restrict K) := by
    intro τ hτ
    have hbase := (hFτmem τ hτ).integrable one_le_two
    have hmul := hbase.bdd_mul hξmeas (c := 1) hξbound
    simpa only [Function.comp_apply, parSlice, F, mul_comm] using hmul
  have hFdiffmem : ∀ τ ∈ Icc s T,
      MemLp (fun x : Vec d => F (u.toFun (x, τ)) - F (u.toFun (x, t₀)))
        2 (volume.restrict K) := by
    intro τ hτ
    exact (hFτmem τ hτ).sub (hFτmem t₀ ht₀)
  have hFdiffSq : ∀ τ ∈ Icc s T,
      (∫ x in K, (F (u.toFun (x, τ)) - F (u.toFun (x, t₀))) ^ 2) ≤
        (C : ℝ) ^ 2 * E τ := by
    intro τ hτ
    have huτ := u.sliceL2loc τ hτ K hKcompact (subset_univ _)
    have hu₀ := u.sliceL2loc t₀ ht₀ K hKcompact (subset_univ _)
    have huDiff := huτ.sub hu₀
    have hIntF := (hFdiffmem τ hτ).integrable_sq
    have hIntU := huDiff.integrable_sq
    have hIntU' : Integrable (fun x : Vec d =>
        (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2) (volume.restrict K) := by
      exact hIntU.congr (Filter.Eventually.of_forall fun _ => rfl)
    calc
      (∫ x in K, (F (u.toFun (x, τ)) - F (u.toFun (x, t₀))) ^ 2) ≤
          ∫ x in K, (C : ℝ) ^ 2 * (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := by
        apply integral_mono hIntF (hIntU'.const_mul ((C : ℝ) ^ 2))
        intro x
        have hpoint := hFLip.dist_le_mul (u.toFun (x, τ)) (u.toFun (x, t₀))
        have hpoint' : |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))| ≤
            (C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| := by
          simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hpoint
        have hCnonneg : 0 ≤ (C : ℝ) := NNReal.coe_nonneg C
        have hA : 0 ≤ |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))| := abs_nonneg _
        have hB : 0 ≤ (C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| :=
          mul_nonneg hCnonneg (abs_nonneg _)
        have hsum : 0 ≤ (C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| +
            |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))| := add_nonneg hB hA
        have hprod : 0 ≤ ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| -
            |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))|) *
            ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)| +
              |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))|) :=
          mul_nonneg (sub_nonneg.mpr hpoint') hsum
        have hsq : |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))| ^ 2 ≤
            ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)|) ^ 2 := by
          nlinarith [hprod]
        calc
          (F (u.toFun (x, τ)) - F (u.toFun (x, t₀))) ^ 2 =
              |F (u.toFun (x, τ)) - F (u.toFun (x, t₀))| ^ 2 := by rw [sq_abs]
          _ ≤ ((C : ℝ) * |u.toFun (x, τ) - u.toFun (x, t₀)|) ^ 2 := hsq
          _ = (C : ℝ) ^ 2 * (u.toFun (x, τ) - u.toFun (x, t₀)) ^ 2 := by
            rw [mul_pow, sq_abs]
      _ = (C : ℝ) ^ 2 * E τ := by
        rw [MeasureTheory.integral_const_mul]
  have hdiffBound : ∀ τ ∈ Icc s T,
      |(∫ x in K, ξ x * F (u.toFun (x, τ))) -
        (∫ x in K, ξ x * F (u.toFun (x, t₀)))| ≤ L * Real.sqrt (E τ) := by
    intro τ hτ
    let G : Vec d → ℝ := fun x => F (u.toFun (x, τ)) - F (u.toFun (x, t₀))
    have hGmem : MemLp G 2 (volume.restrict K) := by
      simpa only [G] using hFdiffmem τ hτ
    have hGint : Integrable G (volume.restrict K) := hGmem.integrable one_le_two
    have hprodInt : Integrable (fun x => ξ x * G x) (volume.restrict K) := by
      have := hGint.bdd_mul hξmeas (c := 1) hξbound
      simpa only [mul_comm] using this
    have hmomentDiff :
        (∫ x in K, ξ x * F (u.toFun (x, τ))) -
          ∫ x in K, ξ x * F (u.toFun (x, t₀)) = ∫ x in K, ξ x * G x := by
      rw [← integral_sub (hFτint τ hτ) (hFτint t₀ ht₀)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp only [G]
      ring_nf
    have hG' : MemL2On K G := hGmem
    have hξ' : MemL2On K ξ := hξmem
    have hupper := PDE.Ch4GreenDecay.integral_mul_le_sqrt hG' hξ'
    have hlower := PDE.Ch4GreenDecay.integral_mul_le_sqrt hG'.neg hξ'
    have hupper' : ∫ x in K, ξ x * G x ≤ Real.sqrt (∫ x in K, G x ^ 2) * Mξ := by
      simpa only [mul_comm, Mξ] using hupper
    have hlower' : -(∫ x in K, ξ x * G x) ≤ Real.sqrt (∫ x in K, G x ^ 2) * Mξ := by
      have heq : ∫ x in K, (-G x) * ξ x = -(∫ x in K, ξ x * G x) := by
        rw [show (fun x : Vec d => (-G x) * ξ x) = fun x => -(ξ x * G x) by
          funext x; ring_nf]
        rw [MeasureTheory.integral_neg]
      calc
        -(∫ x in K, ξ x * G x) = ∫ x in K, (-G x) * ξ x := heq.symm
        _ ≤ Real.sqrt (∫ x in K, (-G x) ^ 2) * Mξ := by
          simpa [Mξ, neg_sq, mul_comm] using hlower
        _ = Real.sqrt (∫ x in K, G x ^ 2) * Mξ := by
          congr 1
          apply congrArg Real.sqrt
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          ring_nf
    have hGabs : |∫ x in K, ξ x * G x| ≤ Real.sqrt (∫ x in K, G x ^ 2) * Mξ :=
      abs_le.mpr ⟨by linarith [hlower'], hupper'⟩
    have hroot : Real.sqrt (∫ x in K, G x ^ 2) ≤ (C : ℝ) * Real.sqrt (E τ) := by
      have hnonneg : 0 ≤ (∫ x in K, G x ^ 2) := integral_nonneg fun x => sq_nonneg _
      have hnonnegE : 0 ≤ E τ := integral_nonneg fun x => sq_nonneg _
      have hsqrt := Real.sqrt_le_sqrt (hFdiffSq τ hτ)
      rw [Real.sqrt_mul (sq_nonneg (C : ℝ)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg C)] at hsqrt
      exact hsqrt
    rw [hmomentDiff]
    calc
      |∫ x in K, ξ x * G x| ≤ Real.sqrt (∫ x in K, G x ^ 2) * Mξ := hGabs
      _ ≤ ((C : ℝ) * Real.sqrt (E τ)) * Mξ :=
        mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
      _ = L * Real.sqrt (E τ) := by dsimp [L]; ring_nf
  have hdist : Tendsto (fun τ => dist
      (∫ x in K, ξ x * F (u.toFun (x, τ)))
      (∫ x in K, ξ x * F (u.toFun (x, t₀)))) (𝓝[Icc s T] t₀) (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun τ => dist_nonneg) ?_ hLlim
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [Real.dist_eq]
    exact hdiffBound τ hτ
  have hsub : Tendsto (fun τ =>
      (∫ x in K, ξ x * F (u.toFun (x, τ))) -
        (∫ x in K, ξ x * F (u.toFun (x, t₀)))) (𝓝[Icc s T] t₀) (𝓝 0) := by
    apply (tendsto_iff_dist_tendsto_zero).2
    simpa only [Real.dist_eq, sub_zero] using hdist
  have hcont := hsub.add_const (∫ x in K, ξ x * F (u.toFun (x, t₀)))
  change Tendsto (fun τ => ∫ x in K, ξ x * F (u.toFun (x, τ)))
    (𝓝[Icc s T] t₀) (𝓝 (∫ x in K, ξ x * F (u.toFun (x, t₀))))
  simpa [sub_add_cancel] using hcont

noncomputable def cauchyNegativeRemainder {d : ℕ} {s T : ℝ}
    (a : ParCoeffField d) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ε R : ℝ) (hR : 0 < R) (z : Vec d × ℝ) : ℝ :=
  cauchyNegativeSource ε (u.toFun z) *
      (cauchyParabolicCutoff s T R hR).toFun z * cauchyEnergyDensity a u z +
    cauchyNegativeFirstIntegral ε (u.toFun z) *
      vecDot (matVecMul (a z) (u.grad z))
        (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z)

theorem cauchySpatialCutoff_zero_outside_closedBall {d : ℕ} (R : ℝ)
    (hR : 0 < R) {x : Vec d}
    (hx : x ∉ euclideanClosedBall 0 (2 * R)) :
    (cauchySpatialCutoff R hR).toFun x = 0 := by
  have hxball : x ∉ euclideanBall 0 (2 * R) := by
    intro hball
    apply hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    have hn := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hball
    rw [sub_zero] at hn ⊢
    exact le_of_lt hn
  exact (cauchySpatialCutoff R hR).eq_zero_of_not_mem_outer hxball

theorem cauchySpatialCutoff_grad_zero_outside_closedBall {d : ℕ} (R : ℝ)
    (hR : 0 < R) {x : Vec d}
    (hx : x ∉ euclideanClosedBall 0 (2 * R)) :
    spaceGradC1 (cauchySpatialCutoff R hR).toFun x = 0 := by
  have hxball : x ∉ euclideanBall 0 (2 * R) := by
    intro hball
    apply hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    have hn := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hball
    rw [sub_zero] at hn ⊢
    exact le_of_lt hn
  have hclass := (cauchySpatialCutoff R hR).classicalGradient_eq_zero_of_not_mem_outer hxball
  have heq : spaceGradC1 (cauchySpatialCutoff R hR).toFun x =
      classicalGradient (cauchySpatialCutoff R hR).toFun x := by
    ext i
    rfl
  rw [heq, hclass]

theorem cauchyNegativeRemainder_cross_bound {d : ℕ}
    {a : ParCoeffField d} {s T : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) (z : Vec d × ℝ) :
    |cauchyNegativeFirstIntegral ε (u.toFun z) *
        vecDot (matVecMul (a z) (u.grad z))
          (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z)| ≤
      (32 / R) * cauchyFluxMajorant a u z := by
  let p := parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z
  let F := PDE.Parabolic.Energy.flux a u z
  have hfirst : |cauchyNegativeFirstIntegral ε (u.toFun z)| ≤ |u.toFun z| :=
    cauchyNegativeFirstIntegral_abs_le_abs ε hε (u.toFun z)
  have hp : vecEuclideanNorm p ≤ 32 / R :=
    cauchyParabolicCutoff_spatialGrad_bound s T R hR z.1 z.2
  have hF : vecEuclideanNorm F ≤ ∑ i : Fin d, |F i| := vecEuclideanNorm_le_sum_abs F
  have hdot := abs_vecDot_le_vecEuclideanNorm_mul F p
  have hnF : 0 ≤ vecEuclideanNorm F := vecEuclideanNorm_nonneg F
  have hnp : 0 ≤ vecEuclideanNorm p := vecEuclideanNorm_nonneg p
  have hsum : 0 ≤ ∑ i : Fin d, |F i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hRcoef : 0 ≤ (32 : ℝ) / R := by positivity
  have huabs : 0 ≤ |u.toFun z| := abs_nonneg _
  calc
    |cauchyNegativeFirstIntegral ε (u.toFun z) * vecDot F p| ≤
      |u.toFun z| * (vecEuclideanNorm F * vecEuclideanNorm p) := by
      rw [abs_mul]
      exact mul_le_mul hfirst hdot (abs_nonneg _) huabs
    _ ≤ |u.toFun z| * ((∑ i : Fin d, |F i|) * (32 / R)) := by
      gcongr
    _ = (32 / R) * cauchyFluxMajorant a u z := by
      simp [F, cauchyFluxMajorant]
      ring_nf

theorem cauchyNegativeRemainder_integrable_Ioc {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    IntegrableOn (cauchyNegativeRemainder a u ε R hR)
      ((univ : Set (Vec d)) ×ˢ Ioc s T) := by
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let ζ : ParCutoff (univ : Set (Vec d)) (Icc s T) :=
    cauchyParabolicCutoff s T R hR
  let uF : Vec d × ℝ → ℝ := fun z => u.toFun z
  let coeff : Vec d × ℝ → ℝ := fun z =>
    cauchyNegativeSource ε (uF z) * ζ.toFun z
  let cross : Vec d × ℝ → ℝ := fun z =>
    cauchyNegativeFirstIntegral ε (uF z) *
      vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ζ.toFun z)
  have hq : IntegrableOn (cauchyEnergyDensity a u) Q := by
    simpa only [Q] using cauchyEnergyDensity_integrable_Ioc ha u ⟨hsT.le, le_rfl⟩
  have hmajor : IntegrableOn (cauchyFluxMajorant a u) Q := by
    simpa only [Q] using cauchyFluxMajorant_integrable_Ioc ha u ⟨hsT.le, le_rfl⟩
  let μ := volume.restrict Q
  have huMeas : AEStronglyMeasurable uF μ := by
    dsimp [uF, μ, Q]
    exact u.memL2.aestronglyMeasurable.mono_measure <|
      Measure.restrict_mono (prod_mono subset_rfl (Ioc_subset_Icc_self)) le_rfl
  have hsourceMeas : AEStronglyMeasurable (fun z => cauchyNegativeSource ε (uF z)) μ :=
    (cauchyNegativeSource_contDiff ε hε).continuous.comp_aestronglyMeasurable huMeas
  have hζMeas : AEStronglyMeasurable ζ.toFun μ := ζ.contDiff.continuous.aestronglyMeasurable
  have hcoeffMeas : AEStronglyMeasurable coeff μ := by
    exact hsourceMeas.mul hζMeas
  have hcoeffBound : ∀ᵐ z ∂μ, ‖coeff z‖ ≤ 1 := by
    filter_upwards [] with z
    dsimp [coeff]
    have hsource0 := cauchyNegativeSource_nonneg ε hε (uF z)
    have hsource1 := cauchyNegativeSource_le_one ε hε (uF z)
    rcases cauchyParabolicCutoff_nonneg_le_one s T R hR z with ⟨hζ0, hζ1⟩
    rw [abs_of_nonneg (mul_nonneg hsource0 hζ0)]
    nlinarith
  have hbulk : Integrable (fun z => coeff z * cauchyEnergyDensity a u z) μ := by
    exact hq.bdd_mul hcoeffMeas (c := 1) hcoeffBound
  have hfirstMeas : AEStronglyMeasurable
      (fun z => cauchyNegativeFirstIntegral ε (uF z)) μ :=
    (cauchyNegativeFirstIntegral_contDiff ε hε).continuous.comp_aestronglyMeasurable huMeas
  have hflux : ∀ i : Fin d, AEStronglyMeasurable
      (fun z => PDE.Parabolic.Energy.flux a u z i) μ := by
    intro i
    exact (PDE.Parabolic.Energy.flux_memLp ha u i).mono_measure
      (Measure.restrict_mono (prod_mono subset_rfl Ioc_subset_Icc_self) le_rfl) |>.aestronglyMeasurable
  have hgradCont : Continuous (parSpaceGrad ζ.toFun) :=
    PDE.ParabCaccioppoli.continuous_parSpaceGrad ζ
  have hdotMeas : AEStronglyMeasurable
      (fun z => vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad ζ.toFun z)) μ := by
    have hdot : AEStronglyMeasurable
        (fun z => vecDot (PDE.Parabolic.Energy.flux a u z) (parSpaceGrad ζ.toFun z)) μ := by
      unfold vecDot
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (hflux i).mul
        (((continuous_apply i).comp hgradCont).aestronglyMeasurable)
    refine hdot.congr ?_
    filter_upwards [] with z
    simp [PDE.Parabolic.Energy.flux]
  have hcrossMeas : AEStronglyMeasurable cross μ := hfirstMeas.mul hdotMeas
  have hcrossInt : Integrable cross μ := by
    refine Integrable.mono' (hmajor.const_mul (32 / R)) hcrossMeas ?_
    filter_upwards [] with z
    dsimp [cross, uF, ζ, μ, Q]
    have h := cauchyNegativeRemainder_cross_bound (a := a) (u := u) ε R hε hR z
    simpa only [PDE.Parabolic.Energy.flux] using h
  change Integrable (fun z => coeff z * cauchyEnergyDensity a u z + cross z) μ
  have hsum := hbulk.add hcrossInt
  have heq : (fun z => coeff z * cauchyEnergyDensity a u z + cross z) =
      cauchyNegativeRemainder a u ε R hR := by
    funext z
    simp [coeff, cross, uF, ζ, cauchyNegativeRemainder]
  rw [heq]
  exact hsum

noncomputable def cauchyNegativeRemainderSlice {d : ℕ} {s T : ℝ}
    (a : ParCoeffField d) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ε R : ℝ) (hR : 0 < R) (τ : ℝ) : ℝ :=
  ∫ x : Vec d, cauchyNegativeRemainder a u ε R hR (x, τ)

theorem cauchyNegativeMoment_eq_integral_univ {d : ℕ} {s T : ℝ}
    (ε R : ℝ) (hR : 0 < R)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (τ : ℝ) :
    cauchyNegativeMoment ε R hR u τ =
      ∫ x : Vec d, (cauchySpatialCutoff R hR).toFun x *
        cauchyNegativeEnergy ε (u.toFun (x, τ)) := by
  let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
  have hset :
      (∫ x in (univ : Set (Vec d)), (cauchySpatialCutoff R hR).toFun x *
        cauchyNegativeEnergy ε (u.toFun (x, τ))) =
      ∫ x in K, (cauchySpatialCutoff R hR).toFun x *
        cauchyNegativeEnergy ε (u.toFun (x, τ)) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ K)]
    intro x hx
    have hxnot : x ∉ euclideanClosedBall 0 (2 * R) := by simpa [K] using hx.2
    rw [cauchySpatialCutoff_zero_outside_closedBall R hR hxnot]
    simp
  calc
    cauchyNegativeMoment ε R hR u τ =
        ∫ x in K, (cauchySpatialCutoff R hR).toFun x *
          cauchyNegativeEnergy ε (u.toFun (x, τ)) := by rfl
    _ = ∫ x in (univ : Set (Vec d)), (cauchySpatialCutoff R hR).toFun x *
          cauchyNegativeEnergy ε (u.toFun (x, τ)) := hset.symm
    _ = ∫ x : Vec d, (cauchySpatialCutoff R hR).toFun x *
          cauchyNegativeEnergy ε (u.toFun (x, τ)) := by rw [setIntegral_univ]

theorem cauchyNegativeMomentWhole_continuousOn {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    ContinuousOn (fun τ => ∫ x : Vec d, (cauchySpatialCutoff R hR).toFun x *
      cauchyNegativeEnergy ε (u.toFun (x, τ))) (Icc s T) := by
  have hlocal := cauchyNegativeMoment_continuousOn hsT ha f hf u hu ε R hε hR
  refine hlocal.congr ?_
  intro τ _
  exact (cauchyNegativeMoment_eq_integral_univ ε R hR u τ).symm

end PDE.Parabolic.Cauchy.Energy
