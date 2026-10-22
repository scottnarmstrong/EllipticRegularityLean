module

public import EllipticRegularity.Parabolic.SliceEstimate.Bridge
public import EllipticRegularity.Parabolic.SliceEstimate.GradTime
public import EllipticRegularity.Parabolic.SliceEstimate.CenterEq

/-!
# The slice identity for `v = ∂ₜu`

For a time-independent coefficient, `v` satisfies the weak-slice identity at every time:
`∫ v(t) ζ - ∫ v(s) ζ = - ∫_s^t ∫ a∇v·∇ζ` for `ζ ∈ C¹_c`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

theorem vecDot_matVecMul_eq_sum (A : Mat d) (g q : Vec d) :
    vecDot (matVecMul A g) q = ∑ j, (∑ i, A i j * q i) * g j := by
  simp only [vecDot, matVecMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem integrableOn_mul_snd {S : Set (Vec d)} (hS : MeasurableSet S) {s t : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f)
    {G : Vec d × ℝ → ℝ} (hG : IntegrableOn G (S ×ˢ Icc s t)) :
    IntegrableOn (fun z : Vec d × ℝ => f z.2 * G z) (S ×ˢ Ioo s t) := by
  have hG' : IntegrableOn G (S ×ˢ Ioo s t) := hG.mono_set (prod_mono subset_rfl Ioo_subset_Icc_self)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := s) (b := t)).exists_bound_of_continuousOn hf.continuousOn
  refine hG'.bdd_mul (hf.comp continuous_snd).aestronglyMeasurable (c := M) ?_
  have hzI : ∀ᵐ z ∂(volume.restrict (S ×ˢ Ioo s t)), z.2 ∈ Ioo s t :=
    (ae_restrict_iff' (hS.prod measurableSet_Ioo)).2 (Eventually.of_forall fun z hz => hz.2)
  filter_upwards [hzI] with z hz
  exact hM z.2 ⟨hz.1.le, hz.2.le⟩

theorem v_slice_identity {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {K' : Set (Vec d)} {δ' : ℝ} (hK'c : IsCompact K') (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    (hK'U : K' ⊆ euclideanBall (0 : Vec d) 1)
    (hK'1U : cthickening δ' K' ⊆ euclideanBall (0 : Vec d) 1) (hζK : tsupport ζ ⊆ K')
    {s t : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0) (ht : t ∈ Ioc (-1 : ℝ) 0) (hst : s < t) :
    IntegrableOn (fun z : Vec d × ℝ => vecDot (matVecMul (a₀ z.1) (v.grad z))
        (spaceGradC1 ζ z.1)) (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) ∧
      (∫ x in euclideanBall (0 : Vec d) 1, v.toFun (x, t) * ζ x) -
          (∫ x in euclideanBall (0 : Vec d) 1, v.toFun (x, s) * ζ x) =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t,
          vecDot (matVecMul (a₀ z.1) (v.grad z)) (spaceGradC1 ζ z.1) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  have hζU : tsupport ζ ⊆ euclideanBall (0 : Vec d) 1 := hζK.trans hK'U
  have hs0 : s < 0 := lt_of_lt_of_le hst ht.2
  obtain ⟨D, hDK, hDδ, hDp, hDq, hDA, -, hDl, hDL, hDW, hDZ⟩ := exists_edata_gen ha u v hv hK'c
    hδ'0 hδ'1 hK'U hK'1U (p := s) hs.1 hs0 (fun _ => 0) contDiff_const (fun _ _ => rfl)
  have hSub : Icc s t ⊆ Ioc (-1 : ℝ) 0 := hI.out hs ht
  have hIoo : Ioo s t ⊆ Ioc s t := Ioo_subset_Ioc_self
  -- flux integrability (for `u` and `v`)
  have hFu := integrableOn_flux_Icc hU hI ha u hζ hζc hζU hs ht
  have hFv := integrableOn_flux_Icc hU hI ha v hζ hζc hζU hs ht
  set Fu : Vec d × ℝ → ℝ := fun z => vecDot (matVecMul (a₀ z.1) (u.grad z)) (spaceGradC1 ζ z.1)
    with hFu_def
  set Fv : Vec d × ℝ → ℝ := fun z => vecDot (matVecMul (a₀ z.1) (v.grad z)) (spaceGradC1 ζ z.1)
    with hFv_def
  have hFvIoc : IntegrableOn Fv (euclideanBall (0 : Vec d) 1 ×ˢ Ioc s t) :=
    hFv.mono_set (prod_mono subset_rfl Ioc_subset_Icc_self)
  refine ⟨hFvIoc, ?_⟩
  -- the weights
  have hAe : ∀ᵐ x ∂(volume.restrict D.K), IsEllipticMatrix lam Lam (a₀ x) := by
    have := D.hAe; rw [hDA, hDl, hDL] at this; exact this
  obtain ⟨Wb, hWb0, hWb⟩ := spaceGradC1_bound hζ hζc
  set hj : Fin d → Vec d → ℝ := fun j y => ∑ i, a₀ y i j * spaceGradC1 ζ y i with hhj
  have hhjm : ∀ j, AEStronglyMeasurable (hj j) (volume.restrict D.K) := fun j => by
    have : AEMeasurable (hj j) (volume.restrict D.K) := by
      refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
      have h1 : AEMeasurable (fun y => a₀ y i j) (volume.restrict D.K) := by
        have := D.hAm i j; rw [hDA] at this; exact this
      exact h1.mul ((spaceGradC1_continuous hζ i).aemeasurable)
    exact this.aestronglyMeasurable
  have hhjb : ∀ j, ∀ᵐ y ∂(volume.restrict D.K), |hj j y| ≤ d * (Lam * Wb) := fun j => by
    filter_upwards [hAe] with y hy
    calc |hj j y| ≤ ∑ i, |a₀ y i j * spaceGradC1 ζ y i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, Lam * Wb := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (abs_apply_le_of_isEllipticMatrix hy i j) (hWb i y) (abs_nonneg _)
            hy.Lam_pos.le
      _ = d * (Lam * Wb) := by simp
  have hps : D.p ≤ s := hDp ▸ le_rfl
  have htq : t ≤ D.q := hDq ▸ ht.2
  -- distributional identity for `Fu`, `Fv` on `K' × (s,t)`
  have hP : ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → tsupport θ ⊆ Ioo s t →
      ∫ z, deriv θ z.2 * Fu z ∂(volume.restrict (K' ×ˢ Ioo s t)) =
        -∫ z, θ z.2 * Fv z ∂(volume.restrict (K' ×ˢ Ioo s t)) := by
    intro θ hθ hθs
    have hJ := fun j => D.grad_time_joint (hhjm j) (hhjb j) j hps hst htq hθ hθs
    rw [hDK] at hJ
    have e1 : ∀ z : Vec d × ℝ, deriv θ z.2 * Fu z = ∑ j, (hj j z.1 * deriv θ z.2) * D.W j z := by
      intro z
      simp only [hFu_def, vecDot_matVecMul_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show D.W j z = u.grad z j from congrFun (hDW j) z]
      simp only [hhj]; ring
    have e2 : ∀ z : Vec d × ℝ, θ z.2 * Fv z = ∑ j, (hj j z.1 * θ z.2) * D.Z j z := by
      intro z
      simp only [hFv_def, vecDot_matVecMul_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show D.Z j z = v.grad z j from congrFun (hDZ j) z]
      simp only [hhj]; ring
    simp_rw [e1, e2]
    rw [integral_finsetSum _ (fun j _ => (hJ j).1), integral_finsetSum _ (fun j _ => (hJ j).2.1),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => (hJ j).2.2
  -- to `B × (s,t)` and iterated integrals
  have hmeasBI : MeasurableSet (euclideanBall (0 : Vec d) 1 ×ˢ Ioo s t) :=
    hU.measurableSet.prod measurableSet_Ioo
  have hzero : ∀ (G : Vec d × ℝ → ℝ), (∀ z : Vec d × ℝ, z.1 ∉ K' → G z = 0) →
      ∫ z, G z ∂(volume.restrict (K' ×ˢ Ioo s t)) =
        ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioo s t, G z := by
    intro G hG
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasBI (prod_mono hK'U subset_rfl) ?_
    intro z hz
    exact hG z (fun h => hz.2 ⟨h, hz.1.2⟩)
  have hvan : ∀ z : Vec d × ℝ, z.1 ∉ K' → spaceGradC1 ζ z.1 = 0 := fun z hz =>
    spaceGradC1_eq_zero_of_notMem (fun h => hz (hζK h))
  set Φu : ℝ → ℝ := fun τ => ∫ x in euclideanBall (0 : Vec d) 1, Fu (x, τ) with hΦu
  set Φv : ℝ → ℝ := fun τ => ∫ x in euclideanBall (0 : Vec d) 1, Fv (x, τ) with hΦv
  have hQ : ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → tsupport θ ⊆ Ioo s t →
      ∫ τ in Ioo s t, deriv θ τ * Φu τ = -∫ τ in Ioo s t, θ τ * Φv τ := by
    intro θ hθ hθs
    have h1 := hP θ hθ hθs
    rw [hzero _ (fun z hz => by simp [hFu_def, hvan z hz, vecDot]),
      hzero _ (fun z hz => by simp [hFv_def, hvan z hz, vecDot])] at h1
    have iu := integrableOn_mul_snd hU.measurableSet (hθ.continuous_deriv le_rfl) hFu
    have iv := integrableOn_mul_snd hU.measurableSet hθ.continuous hFv
    rw [(integral_prod_slices iu).2, (integral_prod_slices iv).2] at h1
    have e1 : ∀ τ, ∫ x in euclideanBall (0 : Vec d) 1, deriv θ τ * Fu (x, τ) = deriv θ τ * Φu τ :=
      fun τ => integral_const_mul _ _
    have e2 : ∀ τ, ∫ x in euclideanBall (0 : Vec d) 1, θ τ * Fv (x, τ) = θ τ * Φv τ :=
      fun τ => integral_const_mul _ _
    simp only [e1, e2] at h1
    exact h1
  have hE := equation_ae hU hI ha u v hu hv hζ hζc hζU hs ht hst
  have hE' : ∀ᵐ τ ∂(volume.restrict (Ioo s t)),
      (∫ x in euclideanBall (0 : Vec d) 1, v.toFun (x, τ) * ζ x) + Φu τ = 0 :=
    ae_restrict_of_ae_restrict_of_subset hIoo hE
  have hmc := slicePairing_continuousOn v hζ hζc hζU
  let m' : ℝ → ℝ := fun τ => slicePairing v ζ (projIcc s t hst.le τ)
  have hm' : Continuous m' :=
    (hmc.mono hSub).comp_continuous continuous_projIcc.subtype_val
      (fun τ => (projIcc s t hst.le τ).2)
  have hΦvI : IntegrableOn Φv (Ioo s t) :=
    (integral_prod_slices hFv).1.mono_set Ioo_subset_Icc_self
  have hdbr := dubois_reymond hst m' Φv hm' hΦvI (fun θ h1 h2 h3 => by
    have step1 : ∫ τ in Ioo s t, m' τ * deriv θ τ = ∫ τ in Ioo s t, (-Φu τ) * deriv θ τ := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hE'] with τ hτ hτm
      have hτ := hτ hτm
      simp only [m', projIcc_of_mem _ (Ioo_subset_Icc_self hτm)]
      have : slicePairing v ζ τ = -Φu τ := by
        unfold slicePairing; linarith
      rw [this]
    rw [step1]
    have step2 : ∫ τ in Ioo s t, (-Φu τ) * deriv θ τ = -∫ τ in Ioo s t, deriv θ τ * Φu τ := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    rw [step2, hQ θ h1 h3, neg_neg]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only; ring)
  simp only [m', projIcc_left, projIcc_right] at hdbr
  unfold slicePairing at hdbr
  have hfub := (integral_prod_slices hFvIoc).2
  rw [hfub, integral_Ioc_eq_integral_Ioo]
  have hΦ : ∫ τ in Ioo s t, Φv τ = ∫ τ in Ioo s t, ∫ x in euclideanBall (0 : Vec d) 1, Fv (x, τ) :=
    rfl
  simp only [hΦ] at hdbr
  linarith

end PDE.Parabolic.Slice
