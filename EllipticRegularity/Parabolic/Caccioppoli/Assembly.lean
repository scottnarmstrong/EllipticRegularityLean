module

public import EllipticRegularity.Parabolic.Caccioppoli.Matrix
public import EllipticRegularity.Parabolic.Caccioppoli.Cutoff

/-!
# Assembly of the parabolic Caccioppoli inequality

Given the energy identity (as the hypothesis `EnergyConclusion`, of the exact shape of the
conclusion of `PDE.parabEnergy`), we prove the Caccioppoli inequality: choice of `t₀`, the
testing identity, the Young inequality with `|a e|² ≤ Λ e·a e`, absorption, and the `ENNReal`
bookkeeping.
-/

@[expose] public section

namespace PDE

namespace ParabCaccioppoli

open MeasureTheory Set Filter Topology

/-- The conclusion of the energy identity (statement of `PDE.parabEnergy`) for given data. -/
def EnergyConclusion {d : ℕ} (a : ParCoeffField d) (U : Set (Vec d)) (I : Set ℝ)
    (u : ParH1Function U I) (φ : ParCutoff U I) : Prop :=
  (∀ t ∈ I, Integrable (fun x => φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) (volume.restrict U)) ∧
    ContinuousOn (fun t => (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) I ∧
    ∀ s t : ℝ, s ∈ I → t ∈ I → s < t →
      IntegrableOn (fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z)
          (U ×ˢ Ioc s t) ∧
      IntegrableOn (fun z => vecDot (matVecMul (a z) (u.grad z))
          (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z))
          (U ×ˢ Ioc s t) ∧
      ((1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2) -
          (1 / 2 : ℝ) * ∫ x in U, φ.toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2 =
        (∫ z in U ×ˢ Ioc s t, u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z) -
          ∫ z in U ×ˢ Ioc s t, vecDot (matVecMul (a z) (u.grad z))
            (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z)

theorem continuous_parTimeDeriv {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (φ : ParCutoff U I) :
    Continuous (parTimeDeriv φ.toFun) :=
  (φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_parSpaceGrad {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (φ : ParCutoff U I) :
    Continuous (parSpaceGrad φ.toFun) :=
  continuous_pi fun _ => (φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_vecNormSq {d : ℕ} : Continuous (vecNormSq : Vec d → ℝ) := by
  have : (vecNormSq : Vec d → ℝ) = fun x => ∑ i, x i ^ 2 := funext vecNormSq_eq_sum_sq
  rw [this]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2

theorem abs_parTimeDeriv_le {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (φ : ParCutoff U I)
    (z : Vec d × ℝ) (C : ℝ) (h : ‖fderiv ℝ φ.toFun z‖ ≤ C) :
    |parTimeDeriv φ.toFun z| ≤ C := by
  have h1 := (fderiv ℝ φ.toFun z).le_opNorm ((0 : Vec d), (1 : ℝ))
  have h2 : ‖((0 : Vec d), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  rw [h2, mul_one] at h1
  unfold parTimeDeriv
  rw [← Real.norm_eq_abs]
  exact h1.trans h

theorem vecNormSq_parSpaceGrad_le {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (φ : ParCutoff U I)
    (z : Vec d × ℝ) (C : ℝ) (h : ‖fderiv ℝ φ.toFun z‖ ≤ C) :
    vecNormSq (parSpaceGrad φ.toFun z) ≤ d * C ^ 2 := by
  rw [vecNormSq_eq_sum_sq]
  have hi : ∀ i : Fin d, parSpaceGrad φ.toFun z i ^ 2 ≤ C ^ 2 := by
    intro i
    have h1 := (fderiv ℝ φ.toFun z).le_opNorm (basisVec i, (0 : ℝ))
    have h2 : ‖(basisVec i, (0 : ℝ))‖ ≤ 1 := by
      rw [Prod.norm_def]
      refine max_le ?_ (by simp)
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      by_cases hj : j = i <;> simp [hj]
    have hC : 0 ≤ C := (norm_nonneg _).trans h
    have h3 : ‖parSpaceGrad φ.toFun z i‖ ≤ C := by
      have : ‖parSpaceGrad φ.toFun z i‖ ≤ ‖fderiv ℝ φ.toFun z‖ * ‖(basisVec i, (0 : ℝ))‖ := h1
      calc _ ≤ ‖fderiv ℝ φ.toFun z‖ * ‖(basisVec i, (0 : ℝ))‖ := this
        _ ≤ ‖fderiv ℝ φ.toFun z‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ ≤ C := by rw [mul_one]; exact h
    rw [Real.norm_eq_abs] at h3
    exact sq_le_sq' (by linarith [abs_le.mp h3]) (abs_le.mp h3).2
  calc ∑ i, parSpaceGrad φ.toFun z i ^ 2 ≤ ∑ _i : Fin d, C ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = d * C ^ 2 := by simp

/-- Positivity of `Λ` from the a.e. ellipticity on a set of positive measure. -/
theorem Lam_pos_of_coeff {d : ℕ} {lam Lam : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    0 < Lam := by
  have hpos : 0 < volume (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    refine ENNReal.mul_pos ?_ ?_
    · exact ((isOpen_euclideanBall (0 : Vec d) 1).measure_pos volume
        ⟨0, by simp [euclideanBall, euclideanSqDist, vecNormSq_eq_sum_sq]⟩).ne'
    · simp
  have : NeBot (ae (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) :=
    ae_neBot.2 (by simpa [Measure.restrict_eq_zero] using hpos.ne')
  obtain ⟨z, hz⟩ := ha.elliptic.exists
  exact hz.Lam_pos


/-- The parabolic Caccioppoli inequality on an open set, assuming the energy identity and `Λ > 0`. -/
theorem caccioppoli_core (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d) (U : Set (Vec d))
    (hU : IsOpen U) (hLam : 0 < Lam)
    (ha : IsParabolicCoeff lam Lam a (U) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (U) (Ioc (-1 : ℝ) 0))
    (φ : ParCutoff (U) (Ioc (-1 : ℝ) 0))
    (t₁ : ℝ) (ht₁ : t₁ ∈ Ioc (-1 : ℝ) 0)
    (henergy : EnergyConclusion a (U) (Ioc (-1 : ℝ) 0) u φ) :
    (∫⁻ z in U ×ˢ Ioc (-1 : ℝ) t₁,
        ENNReal.ofReal (φ.toFun z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z)))) +
      (∫⁻ x in U,
        ENNReal.ofReal (φ.toFun (x, t₁) ^ 2 * u.toFun (x, t₁) ^ 2))
      ≤ ∫⁻ z in U ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) ∧
    (∫⁻ z in U ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)))) < ⊤ := by
  set Q : Set (Vec d × ℝ) := U ×ˢ Ioc (-1 : ℝ) t₁ with hQ
  have hQsub : Q ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := prod_mono subset_rfl (Ioc_subset_Ioc_right ht₁.2)
  have hQmeas : MeasurableSet Q := hU.measurableSet.prod measurableSet_Ioc
  obtain ⟨m, hm1, hm0, hmv⟩ := exists_vanishing_time φ
  obtain ⟨C, hC0, hC⟩ := exists_bound hU φ
  -- choice of t₀
  set t0 : ℝ := (-1 + min m t₁) / 2 with ht0
  have hmt : -1 < min m t₁ := lt_min hm1 ht₁.1
  have ht0a : -1 < t0 := by rw [ht0]; linarith
  have ht0m : t0 < m := by
    have := min_le_left m t₁; rw [ht0]; linarith
  have ht0t : t0 < t₁ := by
    have := min_le_right m t₁; rw [ht0]; linarith
  have ht0I : t0 ∈ Ioc (-1 : ℝ) 0 := ⟨ht0a, ht0t.le.trans ht₁.2⟩
  have hsub0 : U ×ˢ Ioc t0 t₁ ⊆ Q := prod_mono subset_rfl (Ioc_subset_Ioc_left ht0a.le)
  -- vanishing on the early part
  have hearly : ∀ z ∈ Q \ (U ×ˢ Ioc t0 t₁), φ.toFun z = 0 ∧ parTimeDeriv φ.toFun z = 0 ∧
      parSpaceGrad φ.toFun z = 0 := by
    intro z hz
    obtain ⟨⟨hzU, hz1, hz2⟩, hzn⟩ := hz
    have hz2' : z.2 ≤ t0 := by
      by_contra h
      exact hzn ⟨hzU, not_le.1 h, hz2⟩
    obtain ⟨h0, hd⟩ := fderiv_eq_zero_of_lt hU φ m hm0 hmv z ⟨hzU, hz1, hz2'.trans_lt ht0m⟩
    refine ⟨h0, ?_, ?_⟩
    · simp [parTimeDeriv, hd]
    · funext i; simp [parSpaceGrad, hd]
  -- the energy identity with s = t₀, t = t₁
  obtain ⟨hE1int, -, hEid⟩ := henergy
  obtain ⟨hF1, hG, hid⟩ := hEid t0 t₁ ht0I ht₁ ht0t
  have hE0 : ∫ x in U, φ.toFun (x, t0) ^ 2 * u.toFun (x, t0) ^ 2 = 0 := by
    have : ∀ x ∈ U, φ.toFun (x, t0) ^ 2 * u.toFun (x, t0) ^ 2 = 0 := fun x hx => by
      rw [hmv (x, t0) ⟨hx, ht0I⟩ ht0m]; simp
    rw [setIntegral_congr_fun hU.measurableSet this]; simp
  rw [hE0] at hid
  set E1 : ℝ := ∫ x in U, φ.toFun (x, t₁) ^ 2 * u.toFun (x, t₁) ^ 2 with hE1
  have hE1nn : 0 ≤ E1 := integral_nonneg fun x => by positivity
  set F1 : Vec d × ℝ → ℝ := fun z => u.toFun z ^ 2 * φ.toFun z * parTimeDeriv φ.toFun z with hF1def
  set G : Vec d × ℝ → ℝ := fun z => vecDot (matVecMul (a z) (u.grad z))
    (φ.toFun z ^ 2 • u.grad z + (2 * φ.toFun z * u.toFun z) • parSpaceGrad φ.toFun z) with hGdef
  have hF1Q : IntegrableOn F1 Q :=
    hF1.of_forall_sdiff_eq_zero hQmeas fun z hz => by
      obtain ⟨h0, h1, _⟩ := hearly z hz; simp [hF1def, h0]
  have hGQ : IntegrableOn G Q :=
    hG.of_forall_sdiff_eq_zero hQmeas fun z hz => by
      obtain ⟨h0, _, h2⟩ := hearly z hz; simp [hGdef, h0, h2, vecDot]
  have hF1eq : ∫ z in Q, F1 z = ∫ z in U ×ˢ Ioc t0 t₁, F1 z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQmeas hsub0 fun z hz => by
      obtain ⟨h0, h1, _⟩ := hearly z hz; simp [hF1def, h0]
  have hGeq : ∫ z in Q, G z = ∫ z in U ×ˢ Ioc t0 t₁, G z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQmeas hsub0 fun z hz => by
      obtain ⟨h0, _, h2⟩ := hearly z hz; simp [hGdef, h0, h2, vecDot]
  -- key identity: E1 = 2 ∫F1 - 2 ∫G
  have hkey : E1 = 2 * (∫ z in Q, F1 z) - 2 * (∫ z in Q, G z) := by
    linarith [hF1eq, hGeq, hid]
  -- integrability of u² times bounded continuous functions
  have hu2 : Integrable (fun z => u.toFun z ^ 2) (volume.restrict Q) :=
    (u.memL2.integrable_sq).mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hbdd : ∀ (k : Vec d × ℝ → ℝ) (B : ℝ), Continuous k →
      (∀ z ∈ U ×ˢ Ioc (-1 : ℝ) 0, ‖k z‖ ≤ B) →
      Integrable (fun z => u.toFun z ^ 2 * k z) (volume.restrict Q) := by
    intro k B hk hB
    refine hu2.mul_bdd (c := B) hk.aestronglyMeasurable ?_
    exact (ae_restrict_iff' hQmeas).2 (ae_of_all _ fun z hz => hB z (hQsub hz))
  have hcφ : Continuous φ.toFun := φ.contDiff.continuous
  have hJ : Integrable (fun z => u.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z))
      (volume.restrict Q) := by
    refine hbdd _ (d * C ^ 2) (continuous_vecNormSq.comp (continuous_parSpaceGrad φ)) ?_
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
    exact vecNormSq_parSpaceGrad_le φ z C (hC z hz).2
  have hH : Integrable (fun z => u.toFun z ^ 2 *
      (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) (volume.restrict Q) := by
    refine hbdd _ (2 * C * C + 4 * Lam * (d * C ^ 2))
      ((((continuous_const.mul hcφ.abs).mul (continuous_parTimeDeriv φ).abs)).add
        (continuous_const.mul (continuous_vecNormSq.comp (continuous_parSpaceGrad φ)))) ?_
    intro z hz
    have hz' := hC z hz
    have h1 := abs_parTimeDeriv_le φ z C hz'.2
    have h2 := vecNormSq_parSpaceGrad_le φ z C hz'.2
    have h3 : 0 ≤ 2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| := by positivity
    have h4 : 0 ≤ 4 * Lam * vecNormSq (parSpaceGrad φ.toFun z) :=
      mul_nonneg (by positivity) (vecNormSq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg h3 h4)]
    have h5 : 2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| ≤ 2 * C * C := by
      have := mul_le_mul hz'.1 h1 (abs_nonneg _) hC0
      linarith
    have h6 : 4 * Lam * vecNormSq (parSpaceGrad φ.toFun z) ≤ 4 * Lam * (d * C ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- pointwise Young inequality
  set M : Vec d × ℝ → ℝ := fun z => 2 * G z + 4 * Lam * (u.toFun z ^ 2 *
    vecNormSq (parSpaceGrad φ.toFun z)) with hMdef
  have hae : ∀ᵐ z ∂(volume.restrict Q), IsEllipticMatrix lam Lam (a z) :=
    ae_restrict_of_ae_restrict_of_subset hQsub ha.elliptic
  have hyoung : ∀ᵐ z ∂(volume.restrict Q),
      φ.toFun z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z)) ≤ M z :=
    hae.mono fun z hz => young_pointwise hz (u.grad z) (parSpaceGrad φ.toFun z)
      (φ.toFun z) (u.toFun z)
  have hf0 : ∀ᵐ z ∂(volume.restrict Q),
      0 ≤ φ.toFun z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z)) :=
    hae.mono fun z hz => mul_nonneg (sq_nonneg _) (dot_nonneg hz _)
  have hMint : Integrable M (volume.restrict Q) :=
    (hGQ.const_mul 2).add (hJ.const_mul (4 * Lam))
  have hM0 : 0 ≤ᵐ[volume.restrict Q] M := (hf0.and hyoung).mono fun z hz => hz.1.trans hz.2
  have hHnn : 0 ≤ᵐ[volume.restrict Q] fun z => u.toFun z ^ 2 *
      (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)) :=
    ae_of_all _ fun z => mul_nonneg (sq_nonneg _)
      (add_nonneg (by positivity) (mul_nonneg (by positivity) (vecNormSq_nonneg _)))
  -- real integrals
  have hMval : ∫ z in Q, M z = 2 * (∫ z in Q, G z) +
      4 * Lam * (∫ z in Q, u.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z)) := by
    rw [hMdef]
    simp only []
    rw [integral_add (hGQ.const_mul 2) (hJ.const_mul (4 * Lam)), integral_const_mul,
      integral_const_mul]
  have hMnn : 0 ≤ ∫ z in Q, M z := integral_nonneg_of_ae hM0
  have hcmp : (∫ z in Q, M z) + E1 ≤ ∫ z in Q, u.toFun z ^ 2 *
      (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)) := by
    have hlow : Integrable (fun z => 2 * F1 z + 4 * Lam * (u.toFun z ^ 2 *
        vecNormSq (parSpaceGrad φ.toFun z))) (volume.restrict Q) :=
      (hF1Q.const_mul 2).add (hJ.const_mul (4 * Lam))
    have hmono : ∫ z in Q, (2 * F1 z + 4 * Lam * (u.toFun z ^ 2 *
        vecNormSq (parSpaceGrad φ.toFun z))) ≤ ∫ z in Q, u.toFun z ^ 2 *
      (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)) := by
      refine integral_mono hlow hH fun z => ?_
      have h1 : φ.toFun z * parTimeDeriv φ.toFun z ≤
          |φ.toFun z| * |parTimeDeriv φ.toFun z| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (u.toFun z))
      simp only [hF1def]
      linarith [h2]
    have hlowval : ∫ z in Q, (2 * F1 z + 4 * Lam * (u.toFun z ^ 2 *
        vecNormSq (parSpaceGrad φ.toFun z))) = 2 * (∫ z in Q, F1 z) +
        4 * Lam * (∫ z in Q, u.toFun z ^ 2 * vecNormSq (parSpaceGrad φ.toFun z)) := by
      rw [integral_add (hF1Q.const_mul 2) (hJ.const_mul (4 * Lam)), integral_const_mul,
        integral_const_mul]
    rw [hMval, hkey]
    rw [hlowval] at hmono
    linarith
  -- ENNReal bookkeeping
  have hL1 : ∫⁻ z in Q, ENNReal.ofReal (φ.toFun z ^ 2 *
      vecDot (u.grad z) (matVecMul (a z) (u.grad z))) ≤ ENNReal.ofReal (∫ z in Q, M z) := by
    calc _ ≤ ∫⁻ z in Q, ENNReal.ofReal (M z) :=
          lintegral_mono_ae (hyoung.mono fun z hz => ENNReal.ofReal_le_ofReal hz)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hMint hM0).symm
  have hL2 : ∫⁻ x in U, ENNReal.ofReal (φ.toFun (x, t₁) ^ 2 * u.toFun (x, t₁) ^ 2) =
      ENNReal.ofReal E1 :=
    (ofReal_integral_eq_lintegral_ofReal (hE1int t₁ ht₁)
      (ae_of_all _ fun x => by positivity)).symm
  have hR : ∫⁻ z in Q, ENNReal.ofReal (u.toFun z ^ 2 *
      (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) = ENNReal.ofReal (∫ z in Q, u.toFun z ^ 2 *
      (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
        4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) :=
    (ofReal_integral_eq_lintegral_ofReal hH hHnn).symm
  rw [hL2, hR]
  refine ⟨?_, ENNReal.ofReal_lt_top⟩
  calc _ ≤ ENNReal.ofReal (∫ z in Q, M z) + ENNReal.ofReal E1 := add_le_add hL1 le_rfl
    _ = ENNReal.ofReal ((∫ z in Q, M z) + E1) := (ENNReal.ofReal_add hMnn hE1nn).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcmp

/-- The parabolic Caccioppoli inequality on `(-1,0] × B₁`, assuming the energy identity. -/
theorem caccioppoli_of_energy (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (ha : IsParabolicCoeff lam Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (t₁ : ℝ) (ht₁ : t₁ ∈ Ioc (-1 : ℝ) 0)
    (henergy : EnergyConclusion a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u φ) :
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
        ENNReal.ofReal (φ.toFun z ^ 2 * vecDot (u.grad z) (matVecMul (a z) (u.grad z)))) +
      (∫⁻ x in euclideanBall (0 : Vec d) 1,
        ENNReal.ofReal (φ.toFun (x, t₁) ^ 2 * u.toFun (x, t₁) ^ 2))
      ≤ ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z))) ∧
    (∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) t₁,
          ENNReal.ofReal (u.toFun z ^ 2 *
            (2 * |φ.toFun z| * |parTimeDeriv φ.toFun z| +
              4 * Lam * vecNormSq (parSpaceGrad φ.toFun z)))) < ⊤ :=
  caccioppoli_core d lam Lam a _ (isOpen_euclideanBall _ _) (Lam_pos_of_coeff ha) ha u φ t₁ ht₁
    henergy

end ParabCaccioppoli

end PDE
