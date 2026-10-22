/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Chain.H1Solution
public import EllipticRegularity.Parabolic.LocalMax.RenormalizationLimit
public import EllipticRegularity.Parabolic.LocalMax.RenormalizationPointwise

/-! # Renormalization for nonlinearities with only `F''` bounded

`PDE.Parabolic.Chain.weak_solution_renormalization_H1` requires `F` Lipschitz with `F'` and `F''`
bounded. Here we only assume that `F` is `C²` with `F''` bounded (so `F` may grow quadratically).
We compose `F` with the arctan clamp `ψ_M` (`M = n + 1`), apply the bounded version to
`F ∘ ψ_M`, and pass to the limit by dominated convergence.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Chain

variable {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {I : Set ℝ} {a : ParCoeffField d}

/-- A continuous compactly supported function is bounded. -/
theorem exists_abs_le_of_hasCompactSupport {f : Vec d × ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : ∃ B : ℝ, ∀ z, |f z| ≤ B := by
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hs
  exact ⟨B, fun z => by simpa [Real.norm_eq_abs] using hB z⟩

/-- Directional derivatives of a compactly supported `C¹` function are bounded. -/
theorem exists_abs_fderiv_le {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (v : Vec d × ℝ) : ∃ B : ℝ, ∀ z, |fderiv ℝ φ z v| ≤ B := by
  have hc : Continuous fun z => fderiv ℝ φ z v :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsup : HasCompactSupport fun z => fderiv ℝ φ z v :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d × ℝ →L[ℝ] ℝ => L v) (by simp)
  exact exists_abs_le_of_hasCompactSupport hc hsup

/-- The renormalized integrand vanishes off the support of the test function. -/
theorem renormalizedIntegrand_eq_zero_of_notMem {U : Set (Vec d)} {I : Set ℝ}
    (a : ParCoeffField d) (u : ParH1Function U I) (G : ℝ → ℝ) (φ : Vec d × ℝ → ℝ)
    {z : Vec d × ℝ} (hz : z ∉ tsupport φ) : renormalizedIntegrand a u G φ z = 0 := by
  have hfd : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ hz
  have hφ0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
  have htime : parTimeDeriv φ z = 0 := by simp [parTimeDeriv, hfd]
  have hgrad : parSpaceGrad φ z = 0 := by
    ext i
    simp [parSpaceGrad, hfd]
  unfold renormalizedIntegrand
  rw [htime, hgrad, hφ0]
  simp [vecDot]

theorem exists_nnreal_of_abs_le {g : ℝ → ℝ} {K : ℝ} (h : ∀ s, |g s| ≤ K) :
    ∃ C : NNReal, ∀ s, |g s| ≤ C :=
  ⟨K.toNNReal, fun s => (h s).trans (Real.le_coe_toNNReal K)⟩

/-- The clamped nonlinearity satisfies the hypotheses of the bounded-derivative renormalization
theorem. -/
theorem clampF_identity (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hC : ∀ s, |deriv (deriv F) s| ≤ C)
    (φ : ParTestFunction U (interior I)) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) (hst : s < t)
    (hsupp : tsupport φ.toFun ⊆ U ×ˢ Ioo s t) {M : ℝ} (hM : 1 ≤ M) :
    IntegrableOn (renormalizedIntegrand a u (clampF F M) φ.toFun) (U ×ˢ Ioc s t) ∧
      ∫ z in U ×ˢ Ioc s t, renormalizedIntegrand a u (clampF F M) φ.toFun z = 0 := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  have hMne : M ≠ 0 := hM0.ne'
  have hd1 : Differentiable ℝ (clampF F M) :=
    (contDiff_clampF hF M).differentiable (by norm_num)
  have hder : ∀ x, |deriv (clampF F M) x| ≤ |deriv F 0| + C * M / 2 := fun x => by
    rw [deriv_clampF hF hMne]
    exact abs_deriv_clampF_le_const hC hF hM0 x
  refine weak_solution_renormalization_H1 hU hI ha u hu (clampF F M) (contDiff_clampF hF M)
    ?_ (exists_nnreal_of_abs_le hder) ?_ φ hs ht hst hsupp
  · obtain ⟨K, hK⟩ := exists_nnreal_of_abs_le hder
    refine ⟨K, lipschitzWith_of_nnnorm_deriv_le hd1 fun x => ?_⟩
    rw [← NNReal.coe_le_coe]
    simpa using hK x
  · refine exists_nnreal_of_abs_le (K := 3 * C + |deriv F 0|) fun x => ?_
    rw [deriv_deriv_clampF hF hMne x]
    exact abs_deriv_deriv_clampF_le hC hF hM x

/-- Renormalization identity for `C²` nonlinearities with bounded second derivative. -/
theorem weak_solution_renormalization_of_deriv2_bounded (hU : IsOpen U) (hI : I.OrdConnected)
    (ha : IsParabolicCoeff lam Lam a U I) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (hF''bound : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C)
    (φ : ParTestFunction U (interior I)) {s t : ℝ}
    (hs : s ∈ I) (ht : t ∈ I) (hst : s < t)
    (hsupp : tsupport φ.toFun ⊆ U ×ˢ Ioo s t) :
    IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ Ioc s t) ∧
      ∫ z in U ×ˢ Ioc s t, renormalizedIntegrand a u F φ.toFun z = 0 := by
  obtain ⟨C0, hC0⟩ := hF''bound
  set C : ℝ := (C0 : ℝ) with hCdef
  have hC : ∀ x, |deriv (deriv F) x| ≤ C := hC0
  have hCnn : 0 ≤ C := C0.coe_nonneg
  set ν : Measure (Vec d × ℝ) := volume.restrict (U ×ˢ Ioc s t) with hν
  have hsub : U ×ˢ Ioc s t ⊆ U ×ˢ I :=
    prod_mono subset_rfl (Ioc_subset_Icc_self.trans (hI.out hs ht))
  have hνle : ν ≤ volume.restrict (U ×ˢ I) := Measure.restrict_mono hsub le_rfl
  let Fn : ℕ → ℝ → ℝ := fun n => clampF F ((n : ℝ) + 1)
  have hid : ∀ n : ℕ, IntegrableOn (renormalizedIntegrand a u (Fn n) φ.toFun)
      (U ×ˢ Ioc s t) ∧
      ∫ z in U ×ˢ Ioc s t, renormalizedIntegrand a u (Fn n) φ.toFun z = 0 := fun n =>
    clampF_identity hU hI ha u hu hF hC φ hs ht hst hsupp
      (by have : (0 : ℝ) ≤ n := n.cast_nonneg
          linarith)
  -- bounds on the test function
  obtain ⟨Bφ, hBφ⟩ := exists_abs_le_of_hasCompactSupport φ.contDiff.continuous
    φ.hasCompactSupport
  obtain ⟨Bt, hBt⟩ := exists_abs_fderiv_le φ.contDiff φ.hasCompactSupport ((0 : Vec d), (1 : ℝ))
  choose Bi hBi using fun i : Fin d =>
    exists_abs_fderiv_le φ.contDiff φ.hasCompactSupport (basisVec i, (0 : ℝ))
  have hBφ0 : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ 0)
  have hBt0 : 0 ≤ Bt := (abs_nonneg _).trans (hBt 0)
  let BP : ℝ := ∑ i, Bi i ^ 2
  have hBP : ∀ z, vecNormSq (parSpaceGrad φ.toFun z) ≤ BP := by
    intro z
    rw [vecNormSq_eq_sum_sq]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hBi i z
    calc parSpaceGrad φ.toFun z i ^ 2 = |parSpaceGrad φ.toFun z i| ^ 2 := (sq_abs _).symm
      _ ≤ Bi i ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hBP0 : 0 ≤ BP := Finset.sum_nonneg fun i _ => sq_nonneg _
  set Q : ℝ := Real.sqrt BP with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  -- constants
  set f0 : ℝ := |F 0|
  set a0 : ℝ := |deriv F 0|
  have hf0 : 0 ≤ f0 := abs_nonneg _
  have ha0 : 0 ≤ a0 := abs_nonneg _
  set A : ℝ := 3 * C + a0 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set c0 : ℝ := (Bt * (f0 + a0 / 2) + Lam * Q * (a0 / 2)) with hc0
  set c1 : ℝ := (Bt * (a0 / 2 + C) + Lam * Q * (a0 / 2 + C / 2) + A * Lam * Bφ) with hc1
  set K : Set (Vec d × ℝ) := tsupport φ.toFun with hK
  have hKmeas : MeasurableSet K := (isClosed_tsupport _).measurableSet
  let Gb : Vec d × ℝ → ℝ := fun z =>
    K.indicator (fun _ => c0) z + c1 * (u.toFun z ^ 2 + vecNormSq (u.grad z))
  -- integrability of the dominating function
  have hu2 : Integrable (fun z => u.toFun z ^ 2) ν :=
    (u.memL2.mono_measure hνle).integrable_sq
  have hg2 : Integrable (fun z => vecNormSq (u.grad z)) ν := by
    have : (fun z => vecNormSq (u.grad z)) = fun z => ∑ i, u.grad z i ^ 2 :=
      funext fun z => vecNormSq_eq_sum_sq _
    rw [this]
    exact integrable_finsetSum _ fun i _ => ((u.gradMemL2 i).mono_measure hνle).integrable_sq
  have hKfin : ν K ≠ ∞ := by
    have h1 : ν K ≤ volume K := Measure.restrict_apply_le _ _
    exact (h1.trans_lt φ.hasCompactSupport.measure_lt_top).ne
  have hind : Integrable (K.indicator fun _ => c0) ν :=
    (integrable_indicator_iff hKmeas).2 (integrableOn_const hKfin)
  have hGb : Integrable Gb ν := hind.add ((hu2.add hg2).const_mul c1)
  -- the a.e. bound
  have hae : ∀ᵐ z ∂ν, IsEllipticMatrix lam Lam (a z) :=
    ae_restrict_of_ae_restrict_of_subset hsub ha.elliptic
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂ν,
      ‖renormalizedIntegrand a u (Fn n) φ.toFun z‖ ≤ Gb z := by
    intro n
    have hM1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hM0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hMne : ((n : ℝ) + 1) ≠ 0 := hM0.ne'
    filter_upwards [hae] with z hz
    have hLam0 : 0 ≤ Lam := hz.Lam_pos.le
    have hc1nn : 0 ≤ c1 := by positivity
    by_cases hzK : z ∈ K
    · have hGz : Gb z = c0 + c1 * (u.toFun z ^ 2 + vecNormSq (u.grad z)) := by
        simp only [Gb, Set.indicator_of_mem hzK]
      rw [hGz, Real.norm_eq_abs]
      have hn2 : Real.sqrt (vecNormSq (u.grad z)) ^ 2 = vecNormSq (u.grad z) :=
        Real.sq_sqrt (vecNormSq_nonneg _)
      have hPW : |vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ.toFun z)| ≤
          Lam * Real.sqrt (vecNormSq (u.grad z)) * Q := by
        refine (abs_vecDot_matVecMul_le hz _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hBP z)) (by positivity)
      have hPG : |vecDot (matVecMul (a z) (u.grad z)) (u.grad z)| ≤
          Lam * Real.sqrt (vecNormSq (u.grad z)) ^ 2 := by
        rw [hn2]
        exact abs_vecDot_matVecMul_self_le hz _
      have hFv : |Fn n (u.toFun z)| ≤ f0 + a0 * |u.toFun z| + C * u.toFun z ^ 2 :=
        abs_clampF_le hC hF hM0 _
      have hF1 : |deriv (Fn n) (u.toFun z)| ≤ a0 + C * |u.toFun z| := by
        have : deriv (Fn n) = fun x => deriv F (psiM ((n : ℝ) + 1) x) *
            dpsiM ((n : ℝ) + 1) x := deriv_clampF hF hMne
        rw [this]
        exact abs_deriv_clampF_le hC hF hM0 _
      have hF2 : |deriv (deriv (Fn n)) (u.toFun z)| ≤ A := by
        have : deriv (deriv (Fn n)) (u.toFun z) = _ := deriv_deriv_clampF hF hMne _
        rw [this]
        exact abs_deriv_deriv_clampF_le hC hF hM1 _
      have := abs_renorm_terms_le (Fv := Fn n (u.toFun z)) (F1 := deriv (Fn n) (u.toFun z))
        (F2 := deriv (deriv (Fn n)) (u.toFun z)) (τ := parTimeDeriv φ.toFun z)
        (f := φ.toFun z) (x := u.toFun z) (n := Real.sqrt (vecNormSq (u.grad z)))
        (PW := vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ.toFun z))
        (PG := vecDot (matVecMul (a z) (u.grad z)) (u.grad z))
        hf0 ha0 hCnn hA0 hBt0 hBφ0 hLam0 hQ0 hFv hF1 hF2 (hBt _) (hBφ _) hPW hPG
      rw [hn2] at this
      exact this
    · have hGz : Gb z = c1 * (u.toFun z ^ 2 + vecNormSq (u.grad z)) := by
        simp only [Gb, Set.indicator_of_notMem hzK, zero_add]
      rw [hGz, renormalizedIntegrand_eq_zero_of_notMem a u (Fn n) φ.toFun hzK]
      have := vecNormSq_nonneg (u.grad z)
      simp only [norm_zero]
      positivity
  -- pointwise convergence
  have hlim : ∀ z, Tendsto (fun n : ℕ => renormalizedIntegrand a u (Fn n) φ.toFun z) atTop
      (𝓝 (renormalizedIntegrand a u F φ.toFun z)) := by
    intro z
    have h1 := (tendsto_clampF_succ hF (u.toFun z)).mul_const (parTimeDeriv φ.toFun z) |>.neg
    have h2 := (tendsto_deriv_clampF_succ hF (u.toFun z)).mul_const
      (vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ.toFun z))
    have h3 := ((tendsto_deriv_deriv_clampF_succ hF (u.toFun z)).mul_const
      (vecDot (matVecMul (a z) (u.grad z)) (u.grad z))).mul_const (φ.toFun z)
    exact (h1.add h2).add h3
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (renormalizedIntegrand a u (Fn n) φ.toFun) ν :=
    fun n => (hid n).1.aestronglyMeasurable
  have hlim_ae : ∀ᵐ z ∂ν, Tendsto (fun n : ℕ => renormalizedIntegrand a u (Fn n) φ.toFun z)
      atTop (𝓝 (renormalizedIntegrand a u F φ.toFun z)) := Eventually.of_forall hlim
  have hint : IntegrableOn (renormalizedIntegrand a u F φ.toFun) (U ×ˢ Ioc s t) := by
    refine Integrable.mono' hGb (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim_ae) ?_
    have hb : ∀ᵐ z ∂ν, ∀ n : ℕ,
        ‖renormalizedIntegrand a u (Fn n) φ.toFun z‖ ≤ Gb z := ae_all_iff.2 hbound
    filter_upwards [hb] with z hz
    exact le_of_tendsto (hlim z).norm (Eventually.of_forall hz)
  refine ⟨hint, ?_⟩
  have hT := tendsto_integral_of_dominated_convergence Gb hmeas hGb hbound hlim_ae
  have hzero : (fun n : ℕ => ∫ z, renormalizedIntegrand a u (Fn n) φ.toFun z ∂ν) =
      fun _ => (0 : ℝ) := funext fun n => (hid n).2
  rw [hzero] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end PDE.Parabolic.LocalMax
