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
public import EllipticRegularity.Parabolic.Cauchy.Energy.PositivityMoment

/-! # Renormalization identity for Cauchy positivity -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set Filter Topology intervalIntegral

theorem cauchyNegativeRenormalization_test_identity {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsParabolicWeakSolution a univ (Icc s T) u)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) {t : ℝ}
    (ht : t ∈ Icc s T) (hst : s < t) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθsupport : tsupport θ ⊆ Ioo s t) :
    ∫ τ in Ioo s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ =
      ∫ τ in Ioo s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := by
  let F : ℝ → ℝ := cauchyNegativeEnergy ε
  let ξ : Vec d → ℝ := (cauchySpatialCutoff R hR).toFun
  let η : ParCutoff (univ : Set (Vec d)) (Icc s T) :=
    cauchyParabolicCutoff s T R hR
  have htimeSupport : tsupport θ ⊆ interior (Icc s T) :=
    hθsupport.trans (interior_maximal
      (fun τ hτ => ⟨hτ.1.le, hτ.2.le.trans ht.2⟩) isOpen_Ioo)
  let φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T)) :=
    { toFun := fun z => θ z.2 * ξ z.1
      contDiff := PDE.Parabolic.WeakSlice.contDiff_prod hθ
        ((cauchySpatialCutoff R hR).smooth.of_le (by norm_num))
      hasCompactSupport := PDE.Parabolic.WeakSlice.hasCompactSupport_prod hθc
        (cauchySpatialCutoff R hR).hasCompactSupport
      tsupport_subset := by
        exact PDE.Parabolic.WeakSlice.tsupport_prod_subset.trans
          (Set.prod_mono (subset_univ _) htimeSupport) }
  have hφsupport : tsupport φ.toFun ⊆ (univ : Set (Vec d)) ×ˢ Ioo s t := by
    exact PDE.Parabolic.WeakSlice.tsupport_prod_subset.trans
      (Set.prod_mono (subset_univ _) hθsupport)
  have hFcont : ContDiff ℝ 2 F := by
    simpa [F] using (cauchyNegativeEnergy_contDiff ε hε).of_le (by norm_num)
  have hFLip : ∃ C : NNReal, LipschitzWith C F := by
    simpa [F] using cauchyNegativeEnergy_lipschitz ε hε
  have hF'bound : ∃ C' : NNReal, ∀ y : ℝ, |deriv F y| ≤ C' := by
    refine ⟨⟨2 * ε, by positivity⟩, ?_⟩
    intro y
    have h := cauchyNegativeEnergy_deriv_abs_le ε hε y
    change |deriv (cauchyNegativeEnergy ε) y| ≤
      ((⟨2 * ε, by positivity⟩ : NNReal) : ℝ)
    exact h
  have hF''bound : ∃ C' : NNReal, ∀ y : ℝ, |deriv (deriv F) y| ≤ C' := by
    refine ⟨1, ?_⟩
    intro y
    have h := cauchyNegativeEnergy_secondDeriv_abs_le ε hε y
    change |deriv (deriv (cauchyNegativeEnergy ε)) y| ≤ (1 : NNReal)
    exact h
  obtain ⟨hRenInt, hRenZero⟩ := PDE.Parabolic.Chain.weak_solution_renormalization_H1
    isOpen_univ Set.ordConnected_Icc ha u hu F hFcont hFLip hF'bound hF''bound φ
    ⟨le_rfl, hsT.le⟩ ht hst hφsupport
  have hηval (z : Vec d × ℝ) : η.toFun z = ξ z.1 := by
    change (1 : ℝ) * ξ z.1 = ξ z.1
    simp
  have hgradEq (z : Vec d × ℝ) :
      spaceGradC1 ξ z.1 = parSpaceGrad η.toFun z := by
    change spaceGradC1 (cauchySpatialCutoff R hR).toFun z.1 =
      parSpaceGrad (fun w : Vec d × ℝ => (1 : ℝ) *
        (cauchySpatialCutoff R hR).toFun w.1) z
    rw [PDE.Parabolic.WeakSlice.parSpaceGrad_prod
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
      ((cauchySpatialCutoff R hR).smooth.of_le (by norm_num))]
    simp
  have hformula (z : Vec d × ℝ) :
      PDE.Parabolic.Chain.renormalizedIntegrand a u F φ.toFun z =
        -(F (u.toFun z) * deriv θ z.2 * ξ z.1) +
          θ z.2 * cauchyNegativeRemainder a u ε R hR z := by
    unfold PDE.Parabolic.Chain.renormalizedIntegrand
    rw [PDE.Parabolic.WeakSlice.parTimeDeriv_prod hθ
      ((cauchySpatialCutoff R hR).smooth.of_le (by norm_num)),
      PDE.Parabolic.WeakSlice.parSpaceGrad_prod hθ
        ((cauchySpatialCutoff R hR).smooth.of_le (by norm_num)),
      hgradEq z, cauchyNegativeEnergy_secondDeriv ε hε,
      cauchyNegativeEnergy_deriv ε hε]
    dsimp [cauchyNegativeRemainder, F, ξ, η, cauchyParabolicCutoff,
      cauchyEnergyDensity, φ]
    simp only [one_mul]
    rw [PDE.Parabolic.WeakSlice.vecDot_smul_right']
    rw [vecDot_comm (u.grad z) (matVecMul (a z) (u.grad z))]
    ring
  have hremT := cauchyNegativeRemainder_integrable_Ioc hsT ha u ε R hε hR
  have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆
      (univ : Set (Vec d)) ×ˢ Ioc s T :=
    prod_mono subset_rfl (Ioc_subset_Ioc_right ht.2)
  have hrem : IntegrableOn (cauchyNegativeRemainder a u ε R hR)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := hremT.mono_set hQsub
  obtain ⟨Mθ, hMθ⟩ := hθ.continuous.bounded_above_of_compact_support hθc
  have hθmeas : AEStronglyMeasurable (fun z : Vec d × ℝ => θ z.2)
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)) :=
    (hθ.continuous.comp continuous_snd).aestronglyMeasurable
  have hθbound : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
      ‖θ z.2‖ ≤ Mθ := Filter.Eventually.of_forall fun z => hMθ z.2
  have hθrem : IntegrableOn (fun z => θ z.2 * cauchyNegativeRemainder a u ε R hR z)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := hrem.bdd_mul hθmeas (c := Mθ) hθbound
  have hfirst : IntegrableOn
      (fun z => -(F (u.toFun z) * deriv θ z.2 * ξ z.1))
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := by
    have hsub := hRenInt.sub hθrem
    refine hsub.congr ?_
    filter_upwards [] with z
    change PDE.Parabolic.Chain.renormalizedIntegrand a u F φ.toFun z -
      θ z.2 * cauchyNegativeRemainder a u ε R hR z = _
    rw [hformula z]
    ring
  have hsum :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        PDE.Parabolic.Chain.renormalizedIntegrand a u F φ.toFun z) =
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        -(F (u.toFun z) * deriv θ z.2 * ξ z.1)) +
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        θ z.2 * cauchyNegativeRemainder a u ε R hR z := by
    rw [← integral_add hfirst hθrem]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    exact hformula z
  have hfirstFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hfirst
  have hremFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hθrem
  have hinnerFirst (τ : ℝ) :
      ∫ x in (univ : Set (Vec d)),
        -(F (u.toFun (x, τ)) * deriv θ τ * ξ x) =
      -(cauchyNegativeMoment ε R hR u τ * deriv θ τ) := by
    calc
      _ = ∫ x in (univ : Set (Vec d)),
          (-deriv θ τ) * (ξ x * F (u.toFun (x, τ))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        ring_nf
      _ = (-deriv θ τ) * ∫ x in (univ : Set (Vec d)),
          ξ x * F (u.toFun (x, τ)) := by rw [MeasureTheory.integral_const_mul]
      _ = -(cauchyNegativeMoment ε R hR u τ * deriv θ τ) := by
        rw [setIntegral_univ]
        rw [(cauchyNegativeMoment_eq_integral_univ ε R hR u τ)]
        simp only [F, ξ]
        ring
  have hinnerRem (τ : ℝ) :
      ∫ x in (univ : Set (Vec d)),
        θ τ * cauchyNegativeRemainder a u ε R hR (x, τ) =
      θ τ * cauchyNegativeRemainderSlice a u ε R hR τ := by
    rw [MeasureTheory.integral_const_mul]
    simp only [setIntegral_univ, cauchyNegativeRemainderSlice]
  have hfirstTime :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        -(F (u.toFun z) * deriv θ z.2 * ξ z.1)) =
      -∫ τ in Ioc s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ := by
    rw [hfirstFubini.2]
    calc
      _ = ∫ τ in Ioc s t, -(cauchyNegativeMoment ε R hR u τ * deriv θ τ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        exact hinnerFirst τ
      _ = -∫ τ in Ioc s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ := by
        rw [MeasureTheory.integral_neg]
  have hremTime :
      (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        θ z.2 * cauchyNegativeRemainder a u ε R hR z) =
      ∫ τ in Ioc s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := by
    rw [hremFubini.2]
    calc
      _ = ∫ τ in Ioc s t, θ τ * cauchyNegativeRemainderSlice a u ε R hR τ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        exact hinnerRem τ
      _ = ∫ τ in Ioc s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        ring
  have hzθ : ∀ τ, τ ∉ Ioo s t → θ τ = 0 := by
    intro τ hτ
    exact image_eq_zero_of_notMem_tsupport (fun hmem => hτ (hθsupport hmem))
  have hzθ' : ∀ τ, τ ∉ Ioo s t → deriv θ τ = 0 := by
    intro τ hτ
    exact image_eq_zero_of_notMem_tsupport (fun hmem => hτ (hθsupport (tsupport_deriv_subset hmem)))
  have hIocEq :
      ∫ τ in Ioc s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ =
      ∫ τ in Ioc s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := by
    have hsum0 :
        (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          -(F (u.toFun z) * deriv θ z.2 * ξ z.1)) +
        ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          θ z.2 * cauchyNegativeRemainder a u ε R hR z = 0 := by
      rw [← hsum, hRenZero]
    rw [hfirstTime, hremTime] at hsum0
    linarith
  have hleft :
      (∫ τ in Ioc s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ) =
      ∫ τ in Ioo s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      Ioo_subset_Ioc_self (fun τ hτ => by rw [hzθ' τ hτ.2, mul_zero])
  have hright :
      (∫ τ in Ioc s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ) =
      ∫ τ in Ioo s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      Ioo_subset_Ioc_self (fun τ hτ => by rw [hzθ τ hτ.2, mul_zero])
  calc
    _ = ∫ τ in Ioc s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ := hleft.symm
    _ = ∫ τ in Ioc s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := hIocEq
    _ = ∫ τ in Ioo s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ := hright

theorem cauchyNegativeMoment_endpoint_identity {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    cauchyNegativeMoment ε R hR u s - cauchyNegativeMoment ε R hR u t =
      ∫ τ in Ioo s t, cauchyNegativeRemainderSlice a u ε R hR τ := by
  let m₀ : ℝ → ℝ := fun τ => cauchyNegativeMoment ε R hR u τ
  have hmWhole : ContinuousOn (fun τ => ∫ x : Vec d,
      (cauchySpatialCutoff R hR).toFun x *
        cauchyNegativeEnergy ε (u.toFun (x, τ))) (Icc s T) :=
    cauchyNegativeMomentWhole_continuousOn hsT ha f hf u hu ε R hε hR
  have hm₀ : ContinuousOn m₀ (Icc s T) := by
    refine hmWhole.congr ?_
    intro τ _
    change cauchyNegativeMoment ε R hR u τ = _
    exact cauchyNegativeMoment_eq_integral_univ ε R hR u τ
  let clip : ℝ → ℝ := fun τ => max s (min T τ)
  have hclipCont : Continuous clip := by fun_prop
  have hclipRange (τ : ℝ) : clip τ ∈ Icc s T := by
    dsimp [clip]
    exact ⟨le_max_left _ _, max_le hsT.le (min_le_left _ _)⟩
  let m : ℝ → ℝ := fun τ => m₀ (clip τ)
  have hm : Continuous m := by
    have hmc : ContinuousOn m univ := by
      dsimp [m]
      exact hm₀.comp hclipCont.continuousOn (by
        intro τ _
        exact hclipRange τ)
    exact continuousOn_univ.mp hmc
  have hclipEq (τ : ℝ) (hτ : τ ∈ Icc s T) : clip τ = τ := by
    dsimp [clip]
    rw [min_eq_right hτ.2, max_eq_right hτ.1]
  have hremST := cauchyNegativeRemainder_integrable_Ioc hsT ha u ε R hε hR
  have hremFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hremST
  let g : ℝ → ℝ := fun τ => cauchyNegativeRemainderSlice a u ε R hR τ
  have hgST : IntegrableOn g (Ioc s T) := by
    simpa only [g, cauchyNegativeRemainderSlice, setIntegral_univ] using hremFubini.1
  have hgIoc : IntegrableOn g (Ioc s t) := hgST.mono_set
    (Ioc_subset_Ioc_right ht.2)
  have hg : IntegrableOn g (Ioo s t) := hgIoc.mono_set Ioo_subset_Ioc_self
  have hid := PDE.Parabolic.WeakSlice.dubois_reymond hst m g hm hg
    (fun θ hθ hθc hθsupport => by
      calc
        _ = ∫ τ in Ioo s t, cauchyNegativeMoment ε R hR u τ * deriv θ τ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro τ hτ
          simp only [m, m₀]
          rw [hclipEq τ ⟨hτ.1.le, hτ.2.le.trans ht.2⟩]
        _ = ∫ τ in Ioo s t, cauchyNegativeRemainderSlice a u ε R hR τ * θ τ :=
          cauchyNegativeRenormalization_test_identity hsT ha u hu.1 ε R hε hR ht hst
            hθ hθc hθsupport
        _ = ∫ τ in Ioo s t, g τ * θ τ := by simp only [g])
  have hms : m s = cauchyNegativeMoment ε R hR u s := by
    dsimp [m, m₀]
    rw [hclipEq s ⟨le_rfl, hsT.le⟩]
  have hmt : m t = cauchyNegativeMoment ε R hR u t := by
    dsimp [m, m₀]
    rw [hclipEq t ht]
  rw [hms, hmt] at hid
  simpa only [g] using hid

theorem cauchyNegativeEnergy_slice_integrableOn {d : ℕ} {s T : ℝ}
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T)) (ε : ℝ) (hε : 0 < ε)
    {t : ℝ} (ht : t ∈ Icc s T) {K : Set (Vec d)} (hK : IsCompact K) :
    IntegrableOn (fun x => cauchyNegativeEnergy ε (u.toFun (x, t))) K := by
  have hslice := u.sliceL2loc t ht K hK (subset_univ _)
  have hzero : cauchyNegativeEnergy ε 0 = 0 :=
    cauchyNegativeEnergy_zero_of_nonneg ε hε le_rfl
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hLip⟩ := cauchyNegativeEnergy_lipschitz ε hε
  have hcomp : MemLp (fun x => cauchyNegativeEnergy ε (u.toFun (x, t))) 2
      (volume.restrict K) := hLip.comp_memLp hzero hslice
  exact hcomp.integrable one_le_two

theorem cauchyNegativeMoment_initial_zero {d : ℕ}
    {a : ParCoeffField d} {s T : ℝ} (f : Vec d → ℝ)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    cauchyNegativeMoment ε R hR u s = 0 := by
  let K : Set (Vec d) := euclideanClosedBall 0 (2 * R)
  have hK : IsCompact K := isCompact_euclideanClosedBall 0 (by positivity)
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact measurableSet_euclideanClosedBall 0 (2 * R)
  have hinit := cauchy_initial_slice_nonneg a s T f u hu hf0
  have hzero : ∀ᵐ x ∂(volume.restrict K),
      cauchyNegativeEnergy ε (u.toFun (x, s)) = 0 := by
    apply (ae_restrict_iff' hKmeas).2
    filter_upwards [hinit] with x hx hKx
    exact cauchyNegativeEnergy_zero_of_nonneg ε hε hx
  have hzero' : ∀ᵐ x ∂volume, x ∈ K →
      cauchyNegativeEnergy ε (u.toFun (x, s)) = 0 :=
    (ae_restrict_iff' hKmeas).1 hzero
  have hmoment : cauchyNegativeMoment ε R hR u s =
      ∫ x in K, (cauchySpatialCutoff R hR).toFun x *
        cauchyNegativeEnergy ε (u.toFun (x, s)) := by rfl
  rw [hmoment]
  calc
    _ = ∫ x in K, (0 : ℝ) := by
      apply setIntegral_congr_ae hKmeas
      filter_upwards [hzero'] with x hx hKx
      simp [hx hKx]
    _ = 0 := by simp

theorem cauchyNegativeRemainder_integral_lower_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Icc s T) :
    -((32 / R) * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        cauchyFluxMajorant a u z) ≤
      ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        cauchyNegativeRemainder a u ε R hR z := by
  let Qmax : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  let Qt : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let C : ℝ := 32 / R
  have hQsub : Qt ⊆ Qmax := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1, hz.2.2.trans ht.2⟩⟩
  have hQslab : Qt ⊆ (univ : Set (Vec d)) ×ˢ Icc s T := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2.trans ht.2⟩⟩
  have hmajorMax : IntegrableOn (cauchyFluxMajorant a u) Qmax := by
    simpa only [Qmax] using cauchyFluxMajorant_integrable_Ioc ha u ⟨hsT.le, le_rfl⟩
  have hmajorT : IntegrableOn (cauchyFluxMajorant a u) Qt := hmajorMax.mono_set hQsub
  have hmajorNonneg : 0 ≤ᵐ[volume.restrict Qmax] cauchyFluxMajorant a u := by
    refine ae_of_all _ fun z => ?_
    apply mul_nonneg (abs_nonneg _)
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hmajorSetLe :
      ∫ z in Qt, cauchyFluxMajorant a u z ≤
        ∫ z in Qmax, cauchyFluxMajorant a u z :=
    setIntegral_mono_set hmajorMax hmajorNonneg
      (ae_of_all _ fun z hz => hQsub hz)
  have hremMax := cauchyNegativeRemainder_integrable_Ioc hsT ha u ε R hε hR
  have hremT : IntegrableOn (cauchyNegativeRemainder a u ε R hR) Qt :=
    hremMax.mono_set hQsub
  have henergyNonneg : ∀ᵐ z ∂(volume.restrict Qt),
      0 ≤ cauchyEnergyDensity a u z := by
    exact (cauchyEnergyDensity_nonneg_ae ha u).filter_mono
      (ae_mono (Measure.restrict_mono hQslab le_rfl))
  have hpoint : (fun z : Vec d × ℝ => -(C * cauchyFluxMajorant a u z)) ≤ᵐ[
      volume.restrict Qt] (cauchyNegativeRemainder a u ε R hR) := by
    filter_upwards [henergyNonneg] with z hq
    have hsource := cauchyNegativeSource_nonneg ε hε (u.toFun z)
    rcases cauchyParabolicCutoff_nonneg_le_one s T R hR z with ⟨hcut, _⟩
    have hbulk : 0 ≤ cauchyNegativeSource ε (u.toFun z) *
        (cauchyParabolicCutoff s T R hR).toFun z * cauchyEnergyDensity a u z :=
      mul_nonneg (mul_nonneg hsource hcut) hq
    have hcross := cauchyNegativeRemainder_cross_bound
      (a := a) (u := u) ε R hε hR z
    have hcrossLower : -(C * cauchyFluxMajorant a u z) ≤
        cauchyNegativeFirstIntegral ε (u.toFun z) *
          vecDot (matVecMul (a z) (u.grad z))
            (parSpaceGrad (cauchyParabolicCutoff s T R hR).toFun z) := by
      have := (abs_le.mp hcross).1
      simpa only [C] using this
    dsimp [cauchyNegativeRemainder]
    simpa using add_le_add hbulk hcrossLower
  have hremLower :
      ∫ z in Qt, -(C * cauchyFluxMajorant a u z) ≤
        ∫ z in Qt, cauchyNegativeRemainder a u ε R hR z := by
    have hleftInt : IntegrableOn (fun z : Vec d × ℝ =>
        -(C * cauchyFluxMajorant a u z)) Qt := by
      have h := hmajorT.const_mul (-C)
      refine h.congr ?_
      filter_upwards [] with z
      ring
    exact integral_mono_ae hleftInt hremT hpoint
  have hleftEq : (∫ z in Qt, -(C * cauchyFluxMajorant a u z)) =
      -(C * ∫ z in Qt, cauchyFluxMajorant a u z) := by
    rw [show (fun z : Vec d × ℝ => -(C * cauchyFluxMajorant a u z)) =
      fun z => (-C) * cauchyFluxMajorant a u z by funext z; ring,
      MeasureTheory.integral_const_mul]
    ring
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htail : -(C * ∫ z in Qmax, cauchyFluxMajorant a u z) ≤
      ∫ z in Qt, cauchyNegativeRemainder a u ε R hR z := by
    have htail' := hremLower
    rw [hleftEq] at htail'
    calc
      -(C * ∫ z in Qmax, cauchyFluxMajorant a u z) ≤
          -(C * ∫ z in Qt, cauchyFluxMajorant a u z) := by
        have hmul := mul_le_mul_of_nonneg_left hmajorSetLe hC
        linarith
      _ ≤ ∫ z in Qt, cauchyNegativeRemainder a u ε R hR z := htail'
  simpa only [C, Qmax, Qt] using htail

theorem cauchyNegativeMoment_upper_bound {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf : MemLp f 2 volume) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) {t : ℝ}
    (ht : t ∈ Icc s T) (hst : s < t) :
    cauchyNegativeMoment ε R hR u t ≤
      (32 / R) * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        cauchyFluxMajorant a u z := by
  let g : ℝ → ℝ := fun τ => cauchyNegativeRemainderSlice a u ε R hR τ
  let Qt : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s t
  let Qmax : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ Ioc s T
  have hQsub : Qt ⊆ Qmax := by
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1, hz.2.2.trans ht.2⟩⟩
  have hremST := cauchyNegativeRemainder_integrable_Ioc hsT ha u ε R hε hR
  have hremT : IntegrableOn (cauchyNegativeRemainder a u ε R hR) Qt :=
    hremST.mono_set hQsub
  have hFubini := PDE.Parabolic.WeakSlice.integral_prod_slices hremT
  have hFub :
      ∫ z in Qt, cauchyNegativeRemainder a u ε R hR z =
        ∫ τ in Ioc s t, g τ := by
    simpa only [Qt, g, cauchyNegativeRemainderSlice, setIntegral_univ] using hFubini.2
  have htimeEq : (∫ τ in Ioo s t, g τ) = ∫ τ in Ioc s t, g τ := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hendpoint := cauchyNegativeMoment_endpoint_identity hsT ha f hf u hu
    ε R hε hR ht hst
  have hinitial := cauchyNegativeMoment_initial_zero f u hu hf0 ε R hε hR
  have hnegativeMoment : -(cauchyNegativeMoment ε R hR u t) =
      ∫ z in Qt, cauchyNegativeRemainder a u ε R hR z := by
    calc
      _ = cauchyNegativeMoment ε R hR u s - cauchyNegativeMoment ε R hR u t := by
        rw [hinitial]
        ring
      _ = ∫ τ in Ioo s t, g τ := by simpa only [g] using hendpoint
      _ = ∫ τ in Ioc s t, g τ := htimeEq
      _ = ∫ z in Qt, cauchyNegativeRemainder a u ε R hR z := hFub.symm
  have hlower := cauchyNegativeRemainder_integral_lower_bound hsT ha u ε R hε hR ht
  linarith

end PDE.Parabolic.Cauchy.Energy
